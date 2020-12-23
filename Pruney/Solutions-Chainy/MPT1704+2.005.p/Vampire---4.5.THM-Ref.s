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
% DateTime   : Thu Dec  3 13:17:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  141 (1078 expanded)
%              Number of leaves         :   16 ( 221 expanded)
%              Depth                    :   24
%              Number of atoms          :  494 (6217 expanded)
%              Number of equality atoms :   29 ( 652 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f303,f436,f537,f571])).

fof(f571,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f570])).

fof(f570,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f569,f66])).

fof(f66,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_1
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f569,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f562,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_borsuk_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).

fof(f562,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | spl3_3 ),
    inference(resolution,[],[f560,f75])).

fof(f75,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_3
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f560,plain,(
    ! [X1] :
      ( m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK1,X1) ) ),
    inference(forward_demodulation,[],[f559,f94])).

fof(f94,plain,(
    sK2 = g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(backward_demodulation,[],[f34,f92])).

fof(f92,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f41,f89])).

fof(f89,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f34,plain,(
    sK2 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f559,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK1,X1)
      | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f558,f33])).

fof(f33,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f558,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(sK1,X1)
      | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(forward_demodulation,[],[f557,f94])).

fof(f557,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(sK1,X1)
      | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f556,f32])).

fof(f32,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f556,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(sK1,X1)
      | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(forward_demodulation,[],[f555,f94])).

fof(f555,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(sK1,X1)
      | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f554,f36])).

fof(f554,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK1,X1)
      | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f552,f35])).

fof(f35,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f552,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK1,X1)
      | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(superposition,[],[f59,f92])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f537,plain,
    ( ~ spl3_3
    | ~ spl3_29 ),
    inference(avatar_contradiction_clause,[],[f536])).

fof(f536,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(global_subsumption,[],[f31,f74,f518,f525,f528,f535])).

fof(f535,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK0)
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f534,f298])).

fof(f298,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl3_29
  <=> k2_struct_0(sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f534,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK0)
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f533,f74])).

fof(f533,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f254,f528])).

fof(f254,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(superposition,[],[f234,f91])).

fof(f91,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f41,f88])).

fof(f88,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f42,f33])).

fof(f234,plain,(
    ! [X2] :
      ( v4_pre_topc(u1_struct_0(X2),sK0)
      | ~ v1_borsuk_1(X2,sK0)
      | ~ m1_pre_topc(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f231,f38])).

fof(f231,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | v4_pre_topc(u1_struct_0(X2),sK0)
      | ~ v1_borsuk_1(X2,sK0)
      | ~ m1_pre_topc(X2,sK0) ) ),
    inference(resolution,[],[f87,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f61,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v4_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).

fof(f528,plain,
    ( v1_borsuk_1(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(global_subsumption,[],[f29,f523,f527])).

fof(f527,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK1),sK0)
    | v1_borsuk_1(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f471,f74])).

fof(f471,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v1_borsuk_1(sK2,sK0)
    | ~ spl3_29 ),
    inference(superposition,[],[f122,f437])).

fof(f437,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK1)
    | ~ spl3_29 ),
    inference(backward_demodulation,[],[f91,f298])).

fof(f122,plain,(
    ! [X2] :
      ( ~ v4_pre_topc(u1_struct_0(X2),sK0)
      | ~ m1_pre_topc(X2,sK0)
      | v1_borsuk_1(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f119,f38])).

fof(f119,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ v4_pre_topc(u1_struct_0(X2),sK0)
      | v1_borsuk_1(X2,sK0) ) ),
    inference(resolution,[],[f86,f37])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | v1_borsuk_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f60,f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | v1_borsuk_1(X1,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v4_pre_topc(X2,X0)
      | v1_borsuk_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f523,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK0)
    | ~ v1_borsuk_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f255,f518])).

fof(f255,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK0)
    | ~ v1_borsuk_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f234,f92])).

fof(f29,plain,
    ( v1_borsuk_1(sK2,sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f525,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK1),sK0)
    | v1_borsuk_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f208,f518])).

fof(f208,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(superposition,[],[f122,f92])).

fof(f518,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f517,f38])).

fof(f517,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK1,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f516,f74])).

fof(f516,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,X1) ) ),
    inference(forward_demodulation,[],[f515,f94])).

fof(f515,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f514,f33])).

fof(f514,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(forward_demodulation,[],[f513,f94])).

fof(f513,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f512,f32])).

fof(f512,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(forward_demodulation,[],[f511,f94])).

fof(f511,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f510,f36])).

fof(f510,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(sK1)
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f508,f35])).

fof(f508,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(superposition,[],[f58,f92])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f31,plain,
    ( ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f436,plain,(
    spl3_30 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | spl3_30 ),
    inference(subsumption_resolution,[],[f434,f302])).

fof(f302,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl3_30
  <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f434,plain,(
    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(resolution,[],[f433,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f433,plain,(
    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f432,f32])).

fof(f432,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f431,f33])).

fof(f431,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f429,f85])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f40,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f429,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f424,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f424,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f423,f92])).

fof(f423,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v3_pre_topc(X1,sK2)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f422,f91])).

fof(f422,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X1,sK2)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f421,f94])).

fof(f421,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v3_pre_topc(X1,sK2)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f420,f92])).

fof(f420,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f419,f94])).

fof(f419,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f418,f92])).

fof(f418,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f412,f36])).

fof(f412,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f49,f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f303,plain,
    ( spl3_29
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f294,f300,f296])).

fof(f294,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))
    | k2_struct_0(sK2) = k2_struct_0(sK1) ),
    inference(resolution,[],[f293,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f293,plain,(
    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f292,f57])).

fof(f292,plain,(
    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f291,f35])).

fof(f291,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f290,f36])).

fof(f290,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f289,f85])).

fof(f289,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f285,f46])).

fof(f285,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f284,f92])).

fof(f284,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f283,f91])).

fof(f283,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f282,f94])).

fof(f282,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f281,f92])).

fof(f281,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f276,f36])).

fof(f276,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f52,f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f28,f73,f65])).

fof(f28,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (31713)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (31714)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (31724)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % (31717)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.49  % (31703)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (31711)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.49  % (31713)Refutation not found, incomplete strategy% (31713)------------------------------
% 0.20/0.49  % (31713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31713)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (31713)Memory used [KB]: 6140
% 0.20/0.49  % (31713)Time elapsed: 0.075 s
% 0.20/0.49  % (31713)------------------------------
% 0.20/0.49  % (31713)------------------------------
% 0.20/0.49  % (31724)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f577,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f83,f303,f436,f537,f571])).
% 0.20/0.50  fof(f571,plain,(
% 0.20/0.50    ~spl3_1 | spl3_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f570])).
% 0.20/0.50  fof(f570,plain,(
% 0.20/0.50    $false | (~spl3_1 | spl3_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f569,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK0) | ~spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    spl3_1 <=> m1_pre_topc(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f569,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | spl3_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f562,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).
% 0.20/0.50  fof(f562,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | spl3_3),
% 0.20/0.50    inference(resolution,[],[f560,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ~m1_pre_topc(sK2,sK0) | spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    spl3_3 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f560,plain,(
% 0.20/0.50    ( ! [X1] : (m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK1,X1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f559,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    sK2 = g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),
% 0.20/0.50    inference(backward_demodulation,[],[f34,f92])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.50    inference(resolution,[],[f41,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    l1_struct_0(sK1)),
% 0.20/0.50    inference(resolution,[],[f42,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    l1_pre_topc(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    sK2 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f559,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(sK1,X1) | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f558,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    l1_pre_topc(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f558,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_pre_topc(sK2) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK1,X1) | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f557,f94])).
% 0.20/0.50  fof(f557,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(sK1,X1) | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f556,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    v2_pre_topc(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f556,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_pre_topc(sK2) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(sK1,X1) | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f555,f94])).
% 0.20/0.50  fof(f555,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(sK1,X1) | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f554,f36])).
% 0.20/0.50  fof(f554,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,X1) | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f552,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    v2_pre_topc(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f552,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,X1) | m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(superposition,[],[f59,f92])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.20/0.50  fof(f537,plain,(
% 0.20/0.50    ~spl3_3 | ~spl3_29),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f536])).
% 0.20/0.50  fof(f536,plain,(
% 0.20/0.50    $false | (~spl3_3 | ~spl3_29)),
% 0.20/0.50    inference(global_subsumption,[],[f31,f74,f518,f525,f528,f535])).
% 0.20/0.50  fof(f535,plain,(
% 0.20/0.50    v4_pre_topc(k2_struct_0(sK1),sK0) | (~spl3_3 | ~spl3_29)),
% 0.20/0.50    inference(forward_demodulation,[],[f534,f298])).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    k2_struct_0(sK2) = k2_struct_0(sK1) | ~spl3_29),
% 0.20/0.50    inference(avatar_component_clause,[],[f296])).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    spl3_29 <=> k2_struct_0(sK2) = k2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.50  fof(f534,plain,(
% 0.20/0.50    v4_pre_topc(k2_struct_0(sK2),sK0) | (~spl3_3 | ~spl3_29)),
% 0.20/0.50    inference(subsumption_resolution,[],[f533,f74])).
% 0.20/0.50  fof(f533,plain,(
% 0.20/0.50    v4_pre_topc(k2_struct_0(sK2),sK0) | ~m1_pre_topc(sK2,sK0) | (~spl3_3 | ~spl3_29)),
% 0.20/0.50    inference(subsumption_resolution,[],[f254,f528])).
% 0.20/0.50  fof(f254,plain,(
% 0.20/0.50    v4_pre_topc(k2_struct_0(sK2),sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0)),
% 0.20/0.50    inference(superposition,[],[f234,f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.20/0.50    inference(resolution,[],[f41,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    l1_struct_0(sK2)),
% 0.20/0.50    inference(resolution,[],[f42,f33])).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    ( ! [X2] : (v4_pre_topc(u1_struct_0(X2),sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X2,sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f231,f38])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ( ! [X2] : (~l1_pre_topc(sK0) | v4_pre_topc(u1_struct_0(X2),sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X2,sK0)) )),
% 0.20/0.50    inference(resolution,[],[f87,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(u1_struct_0(X1),X0) | ~v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f61,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(u1_struct_0(X1),X0) | ~v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v4_pre_topc(X2,X0) | ~v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).
% 0.20/0.50  fof(f528,plain,(
% 0.20/0.50    v1_borsuk_1(sK2,sK0) | (~spl3_3 | ~spl3_29)),
% 0.20/0.50    inference(global_subsumption,[],[f29,f523,f527])).
% 0.20/0.50  fof(f527,plain,(
% 0.20/0.50    ~v4_pre_topc(k2_struct_0(sK1),sK0) | v1_borsuk_1(sK2,sK0) | (~spl3_3 | ~spl3_29)),
% 0.20/0.50    inference(subsumption_resolution,[],[f471,f74])).
% 0.20/0.50  fof(f471,plain,(
% 0.20/0.50    ~v4_pre_topc(k2_struct_0(sK1),sK0) | ~m1_pre_topc(sK2,sK0) | v1_borsuk_1(sK2,sK0) | ~spl3_29),
% 0.20/0.50    inference(superposition,[],[f122,f437])).
% 0.20/0.50  fof(f437,plain,(
% 0.20/0.50    u1_struct_0(sK2) = k2_struct_0(sK1) | ~spl3_29),
% 0.20/0.50    inference(backward_demodulation,[],[f91,f298])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ( ! [X2] : (~v4_pre_topc(u1_struct_0(X2),sK0) | ~m1_pre_topc(X2,sK0) | v1_borsuk_1(X2,sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f119,f38])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X2,sK0) | ~v4_pre_topc(u1_struct_0(X2),sK0) | v1_borsuk_1(X2,sK0)) )),
% 0.20/0.50    inference(resolution,[],[f86,f37])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | v1_borsuk_1(X1,X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f60,f43])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(u1_struct_0(X1),X0) | v1_borsuk_1(X1,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v4_pre_topc(X2,X0) | v1_borsuk_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f523,plain,(
% 0.20/0.50    v4_pre_topc(k2_struct_0(sK1),sK0) | ~v1_borsuk_1(sK1,sK0) | ~spl3_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f255,f518])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    v4_pre_topc(k2_struct_0(sK1),sK0) | ~v1_borsuk_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(superposition,[],[f234,f92])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    v1_borsuk_1(sK2,sK0) | v1_borsuk_1(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f525,plain,(
% 0.20/0.50    ~v4_pre_topc(k2_struct_0(sK1),sK0) | v1_borsuk_1(sK1,sK0) | ~spl3_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f208,f518])).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    ~v4_pre_topc(k2_struct_0(sK1),sK0) | ~m1_pre_topc(sK1,sK0) | v1_borsuk_1(sK1,sK0)),
% 0.20/0.50    inference(superposition,[],[f122,f92])).
% 0.20/0.50  fof(f518,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK0) | ~spl3_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f517,f38])).
% 0.20/0.50  fof(f517,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | m1_pre_topc(sK1,sK0) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f516,f74])).
% 0.20/0.50  fof(f516,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,X1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f515,f94])).
% 0.20/0.50  fof(f515,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_pre_topc(X1) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f514,f33])).
% 0.20/0.50  fof(f514,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_pre_topc(sK2) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f513,f94])).
% 0.20/0.50  fof(f513,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f512,f32])).
% 0.20/0.50  fof(f512,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_pre_topc(sK2) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f511,f94])).
% 0.20/0.50  fof(f511,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f510,f36])).
% 0.20/0.50  fof(f510,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f508,f35])).
% 0.20/0.50  fof(f508,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.20/0.50    inference(superposition,[],[f58,f92])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    m1_pre_topc(sK2,sK0) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f73])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f436,plain,(
% 0.20/0.50    spl3_30),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f435])).
% 0.20/0.50  fof(f435,plain,(
% 0.20/0.50    $false | spl3_30),
% 0.20/0.50    inference(subsumption_resolution,[],[f434,f302])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    ~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) | spl3_30),
% 0.20/0.50    inference(avatar_component_clause,[],[f300])).
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    spl3_30 <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.50  fof(f434,plain,(
% 0.20/0.50    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))),
% 0.20/0.50    inference(resolution,[],[f433,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f433,plain,(
% 0.20/0.50    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f432,f32])).
% 0.20/0.50  fof(f432,plain,(
% 0.20/0.50    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~v2_pre_topc(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f431,f33])).
% 0.20/0.50  fof(f431,plain,(
% 0.20/0.50    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f429,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f40,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.50  fof(f429,plain,(
% 0.20/0.50    ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.20/0.50    inference(resolution,[],[f424,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.20/0.50  fof(f424,plain,(
% 0.20/0.50    ( ! [X1] : (~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f423,f92])).
% 0.20/0.50  fof(f423,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | ~v3_pre_topc(X1,sK2) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f422,f91])).
% 0.20/0.50  fof(f422,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X1,sK2) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f421,f94])).
% 0.20/0.50  fof(f421,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,sK2) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f420,f92])).
% 0.20/0.50  fof(f420,plain,(
% 0.20/0.50    ( ! [X1] : (~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f419,f94])).
% 0.20/0.50  fof(f419,plain,(
% 0.20/0.50    ( ! [X1] : (~v3_pre_topc(X1,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f418,f92])).
% 0.20/0.50  fof(f418,plain,(
% 0.20/0.50    ( ! [X1] : (~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f412,f36])).
% 0.20/0.50  fof(f412,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_pre_topc(sK1) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(resolution,[],[f49,f35])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    spl3_29 | ~spl3_30),
% 0.20/0.50    inference(avatar_split_clause,[],[f294,f300,f296])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    ~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) | k2_struct_0(sK2) = k2_struct_0(sK1)),
% 0.20/0.50    inference(resolution,[],[f293,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.20/0.50    inference(resolution,[],[f292,f57])).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f291,f35])).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~v2_pre_topc(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f290,f36])).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f289,f85])).
% 0.20/0.50  fof(f289,plain,(
% 0.20/0.50    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.20/0.50    inference(resolution,[],[f285,f46])).
% 0.20/0.50  fof(f285,plain,(
% 0.20/0.50    ( ! [X1] : (~v3_pre_topc(X1,sK1) | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f284,f92])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f283,f91])).
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f282,f94])).
% 0.20/0.50  fof(f282,plain,(
% 0.20/0.50    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f281,f92])).
% 0.20/0.50  fof(f281,plain,(
% 0.20/0.50    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f276,f36])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_pre_topc(sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.50    inference(resolution,[],[f52,f35])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl3_1 | spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f73,f65])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (31724)------------------------------
% 0.20/0.50  % (31724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31724)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (31724)Memory used [KB]: 11001
% 0.20/0.50  % (31724)Time elapsed: 0.039 s
% 0.20/0.50  % (31724)------------------------------
% 0.20/0.50  % (31724)------------------------------
% 0.20/0.50  % (31696)Success in time 0.144 s
%------------------------------------------------------------------------------
