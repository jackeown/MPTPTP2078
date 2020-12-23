%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t17_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:04 EDT 2019

% Result     : Theorem 3.01s
% Output     : Refutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  246 (1336 expanded)
%              Number of leaves         :   42 ( 337 expanded)
%              Depth                    :   26
%              Number of atoms          : 1207 (13926 expanded)
%              Number of equality atoms :  115 (1187 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15332,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f184,f399,f413,f421,f423,f426,f435,f439,f505,f831,f835,f1192,f1194,f1315,f1352,f1397,f1406,f1414,f1430,f1494,f3000,f3156,f15025,f15270,f15298,f15324])).

fof(f15324,plain,
    ( spl11_2
    | ~ spl11_143
    | ~ spl11_5
    | ~ spl11_7
    | spl11_252
    | ~ spl11_57
    | ~ spl11_59
    | ~ spl11_61
    | ~ spl11_147
    | ~ spl11_219
    | ~ spl11_1828 ),
    inference(avatar_split_clause,[],[f15323,f15265,f1190,f827,f428,f419,f416,f1401,f182,f179,f821,f15020])).

fof(f15020,plain,
    ( spl11_2
  <=> v1_waybel_7(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f821,plain,
    ( spl11_143
  <=> ~ v3_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_143])])).

fof(f179,plain,
    ( spl11_5
  <=> ~ v12_waybel_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f182,plain,
    ( spl11_7
  <=> ~ v1_waybel_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1401,plain,
    ( spl11_252
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_252])])).

fof(f416,plain,
    ( spl11_57
  <=> ~ l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).

fof(f419,plain,
    ( spl11_59
  <=> ~ v2_lattice3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f428,plain,
    ( spl11_61
  <=> ~ v5_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f827,plain,
    ( spl11_147
  <=> ~ v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_147])])).

fof(f1190,plain,
    ( spl11_219
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_219])])).

fof(f15265,plain,
    ( spl11_1828
  <=> r2_hidden(sK5(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1828])])).

fof(f15323,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ v3_orders_2(sK1)
    | v1_waybel_7(sK2,sK1)
    | ~ spl11_1828 ),
    inference(forward_demodulation,[],[f15314,f379])).

fof(f379,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f375])).

fof(f375,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f372,f109])).

fof(f109,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_7(X2,X1)
                | ~ v12_waybel_0(X2,X1)
                | ~ v1_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X2,X0)
              & v12_waybel_0(X2,X0)
              & v1_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v1_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_7(X2,X1)
                | ~ v12_waybel_0(X2,X1)
                | ~ v1_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X2,X0)
              & v12_waybel_0(X2,X0)
              & v1_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v1_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & v2_lattice3(X1)
              & v1_lattice3(X1)
              & v5_orders_2(X1)
              & v4_orders_2(X1)
              & v3_orders_2(X1) )
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_waybel_7(X2,X0)
                    & v12_waybel_0(X2,X0)
                    & v1_waybel_0(X2,X0)
                    & ~ v1_xboole_0(X2) )
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                    & v1_waybel_7(X2,X1)
                    & v12_waybel_0(X2,X1)
                    & v1_waybel_0(X2,X1)
                    & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & v2_lattice3(X1)
            & v1_lattice3(X1)
            & v5_orders_2(X1)
            & v4_orders_2(X1)
            & v3_orders_2(X1) )
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X2,X0)
                  & v12_waybel_0(X2,X0)
                  & v1_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_7(X2,X1)
                  & v12_waybel_0(X2,X1)
                  & v1_waybel_0(X2,X1)
                  & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',t17_waybel_7)).

fof(f372,plain,(
    ! [X6,X7] :
      ( g1_orders_2(X6,X7) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK0) = X6 ) ),
    inference(resolution,[],[f360,f115])).

fof(f115,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f360,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(X1,X2) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) ),
    inference(resolution,[],[f151,f118])).

fof(f118,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',dt_u1_orders_2)).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',free_g1_orders_2)).

fof(f15314,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_orders_2(sK1)
    | v1_waybel_7(sK2,sK1)
    | ~ spl11_1828 ),
    inference(resolution,[],[f15266,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',d1_waybel_7)).

fof(f15266,plain,
    ( r2_hidden(sK5(sK1,sK2),sK2)
    | ~ spl11_1828 ),
    inference(avatar_component_clause,[],[f15265])).

fof(f15298,plain,
    ( ~ spl11_246
    | ~ spl11_250
    | ~ spl11_254
    | ~ spl11_260
    | ~ spl11_272
    | spl11_1831 ),
    inference(avatar_contradiction_clause,[],[f15294])).

fof(f15294,plain,
    ( $false
    | ~ spl11_246
    | ~ spl11_250
    | ~ spl11_254
    | ~ spl11_260
    | ~ spl11_272
    | ~ spl11_1831 ),
    inference(resolution,[],[f15269,f4184])).

fof(f4184,plain,
    ( r2_hidden(k12_lattice3(sK0,sK4(sK1,sK2),sK5(sK1,sK2)),sK2)
    | ~ spl11_246
    | ~ spl11_250
    | ~ spl11_254
    | ~ spl11_260
    | ~ spl11_272 ),
    inference(backward_demodulation,[],[f2872,f1493])).

fof(f1493,plain,
    ( r2_hidden(k12_lattice3(sK1,sK4(sK1,sK2),sK5(sK1,sK2)),sK2)
    | ~ spl11_272 ),
    inference(avatar_component_clause,[],[f1492])).

fof(f1492,plain,
    ( spl11_272
  <=> r2_hidden(k12_lattice3(sK1,sK4(sK1,sK2),sK5(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_272])])).

fof(f2872,plain,
    ( k12_lattice3(sK0,sK4(sK1,sK2),sK5(sK1,sK2)) = k12_lattice3(sK1,sK4(sK1,sK2),sK5(sK1,sK2))
    | ~ spl11_246
    | ~ spl11_250
    | ~ spl11_254
    | ~ spl11_260 ),
    inference(resolution,[],[f1871,f1405])).

fof(f1405,plain,
    ( m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK0))
    | ~ spl11_254 ),
    inference(avatar_component_clause,[],[f1404])).

fof(f1404,plain,
    ( spl11_254
  <=> m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_254])])).

fof(f1871,plain,
    ( ! [X25] :
        ( ~ m1_subset_1(X25,u1_struct_0(sK0))
        | k12_lattice3(sK0,sK4(sK1,sK2),X25) = k12_lattice3(sK1,sK4(sK1,sK2),X25) )
    | ~ spl11_246
    | ~ spl11_250
    | ~ spl11_260 ),
    inference(resolution,[],[f1856,f1429])).

fof(f1429,plain,
    ( m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | ~ spl11_260 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f1428,plain,
    ( spl11_260
  <=> m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_260])])).

fof(f1856,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k12_lattice3(sK0,X4,X5) = k12_lattice3(sK1,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_246
    | ~ spl11_250 ),
    inference(duplicate_literal_removal,[],[f1854])).

fof(f1854,plain,
    ( ! [X4,X5] :
        ( k12_lattice3(sK0,X4,X5) = k12_lattice3(sK1,X4,X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_246
    | ~ spl11_250 ),
    inference(superposition,[],[f1351,f1831])).

fof(f1831,plain,
    ( ! [X2,X3] :
        ( k12_lattice3(sK1,X2,X3) = k2_yellow_0(sK0,k2_tarski(X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl11_246 ),
    inference(duplicate_literal_removal,[],[f1827])).

fof(f1827,plain,
    ( ! [X2,X3] :
        ( k12_lattice3(sK1,X2,X3) = k2_yellow_0(sK0,k2_tarski(X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl11_246 ),
    inference(superposition,[],[f1314,f1765])).

fof(f1765,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK0,k2_tarski(X0,X1)) = k2_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f115,f1755])).

fof(f1755,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | k2_yellow_0(sK0,k2_tarski(X0,X1)) = k2_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(equality_resolution,[],[f1033])).

fof(f1033,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | k2_yellow_0(sK1,k2_tarski(X1,X2)) = k2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f108,f1032])).

fof(f1032,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK1)
      | k2_yellow_0(sK1,k2_tarski(X1,X2)) = k2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f1031,f380])).

fof(f380,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    inference(backward_demodulation,[],[f379,f109])).

fof(f1031,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK1)
      | k2_yellow_0(sK1,k2_tarski(X1,X2)) = k2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f1029,f379])).

fof(f1029,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_orders_2(sK1)
      | k2_yellow_0(sK1,k2_tarski(X1,X2)) = k2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f121,f890])).

fof(f890,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f107,f108,f889])).

fof(f889,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK1)
      | r2_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ v2_lattice3(sK1) ) ),
    inference(forward_demodulation,[],[f888,f379])).

fof(f888,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r2_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ v2_lattice3(sK1) ) ),
    inference(forward_demodulation,[],[f886,f379])).

fof(f886,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r2_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ v2_lattice3(sK1) ) ),
    inference(resolution,[],[f141,f105])).

fof(f105,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',t21_yellow_0)).

fof(f107,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r2_yellow_0(X0,X2)
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',t27_yellow_0)).

fof(f108,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f1314,plain,
    ( ! [X4,X5] :
        ( k12_lattice3(sK1,X4,X5) = k2_yellow_0(sK1,k2_tarski(X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_246 ),
    inference(avatar_component_clause,[],[f1313])).

fof(f1313,plain,
    ( spl11_246
  <=> ! [X5,X4] :
        ( k12_lattice3(sK1,X4,X5) = k2_yellow_0(sK1,k2_tarski(X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_246])])).

fof(f1351,plain,
    ( ! [X4,X5] :
        ( k12_lattice3(sK0,X4,X5) = k2_yellow_0(sK0,k2_tarski(X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_250 ),
    inference(avatar_component_clause,[],[f1350])).

fof(f1350,plain,
    ( spl11_250
  <=> ! [X5,X4] :
        ( k12_lattice3(sK0,X4,X5) = k2_yellow_0(sK0,k2_tarski(X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_250])])).

fof(f15269,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK4(sK1,sK2),sK5(sK1,sK2)),sK2)
    | ~ spl11_1831 ),
    inference(avatar_component_clause,[],[f15268])).

fof(f15268,plain,
    ( spl11_1831
  <=> ~ r2_hidden(k12_lattice3(sK0,sK4(sK1,sK2),sK5(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1831])])).

fof(f15270,plain,
    ( spl11_1828
    | ~ spl11_255
    | ~ spl11_1831
    | ~ spl11_246
    | ~ spl11_250
    | ~ spl11_254
    | ~ spl11_260
    | ~ spl11_1810 ),
    inference(avatar_split_clause,[],[f15245,f15023,f1428,f1404,f1350,f1313,f15268,f2360,f15265])).

fof(f2360,plain,
    ( spl11_255
  <=> ~ m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_255])])).

fof(f15023,plain,
    ( spl11_1810
  <=> ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK4(sK1,sK2)),sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1810])])).

fof(f15245,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK4(sK1,sK2),sK5(sK1,sK2)),sK2)
    | ~ m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK5(sK1,sK2),sK2)
    | ~ spl11_246
    | ~ spl11_250
    | ~ spl11_254
    | ~ spl11_260
    | ~ spl11_1810 ),
    inference(superposition,[],[f15024,f7055])).

fof(f7055,plain,
    ( k12_lattice3(sK0,sK4(sK1,sK2),sK5(sK1,sK2)) = k12_lattice3(sK0,sK5(sK1,sK2),sK4(sK1,sK2))
    | ~ spl11_246
    | ~ spl11_250
    | ~ spl11_254
    | ~ spl11_260 ),
    inference(forward_demodulation,[],[f3388,f2872])).

fof(f3388,plain,
    ( k12_lattice3(sK0,sK5(sK1,sK2),sK4(sK1,sK2)) = k12_lattice3(sK1,sK4(sK1,sK2),sK5(sK1,sK2))
    | ~ spl11_246
    | ~ spl11_250
    | ~ spl11_254
    | ~ spl11_260 ),
    inference(resolution,[],[f2761,f1429])).

fof(f2761,plain,
    ( ! [X27] :
        ( ~ m1_subset_1(X27,u1_struct_0(sK0))
        | k12_lattice3(sK0,sK5(sK1,sK2),X27) = k12_lattice3(sK1,X27,sK5(sK1,sK2)) )
    | ~ spl11_246
    | ~ spl11_250
    | ~ spl11_254 ),
    inference(resolution,[],[f1857,f1405])).

fof(f1857,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k12_lattice3(sK0,X3,X2) = k12_lattice3(sK1,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl11_246
    | ~ spl11_250 ),
    inference(duplicate_literal_removal,[],[f1853])).

fof(f1853,plain,
    ( ! [X2,X3] :
        ( k12_lattice3(sK0,X3,X2) = k12_lattice3(sK1,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl11_246
    | ~ spl11_250 ),
    inference(superposition,[],[f1353,f1831])).

fof(f1353,plain,
    ( ! [X0,X1] :
        ( k12_lattice3(sK0,X0,X1) = k2_yellow_0(sK0,k2_tarski(X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_250 ),
    inference(superposition,[],[f1351,f144])).

fof(f144,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',commutativity_k2_tarski)).

fof(f15024,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK4(sK1,sK2)),sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK2) )
    | ~ spl11_1810 ),
    inference(avatar_component_clause,[],[f15023])).

fof(f15025,plain,
    ( spl11_2
    | ~ spl11_143
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_57
    | ~ spl11_59
    | ~ spl11_61
    | ~ spl11_147
    | spl11_1810
    | ~ spl11_219
    | ~ spl11_260 ),
    inference(avatar_split_clause,[],[f15018,f1428,f1190,f15023,f827,f428,f419,f416,f182,f179,f821,f15020])).

fof(f15018,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k12_lattice3(sK0,X0,sK4(sK1,sK2)),sK2)
        | r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK1)
        | ~ v5_orders_2(sK1)
        | ~ v2_lattice3(sK1)
        | ~ l1_orders_2(sK1)
        | ~ v1_waybel_0(sK2,sK1)
        | ~ v12_waybel_0(sK2,sK1)
        | ~ v3_orders_2(sK1)
        | v1_waybel_7(sK2,sK1) )
    | ~ spl11_260 ),
    inference(forward_demodulation,[],[f15017,f379])).

fof(f15017,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK4(sK1,sK2)),sK2)
        | r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK1)
        | ~ v5_orders_2(sK1)
        | ~ v2_lattice3(sK1)
        | ~ l1_orders_2(sK1)
        | ~ v1_waybel_0(sK2,sK1)
        | ~ v12_waybel_0(sK2,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_orders_2(sK1)
        | v1_waybel_7(sK2,sK1) )
    | ~ spl11_260 ),
    inference(resolution,[],[f4455,f1429])).

fof(f4455,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(sK4(X18,sK2),u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X19,sK4(X18,sK2)),sK2)
      | r2_hidden(X19,sK2)
      | ~ m1_subset_1(X19,u1_struct_0(sK0))
      | ~ v4_orders_2(X18)
      | ~ v5_orders_2(X18)
      | ~ v2_lattice3(X18)
      | ~ l1_orders_2(X18)
      | ~ v1_waybel_0(sK2,X18)
      | ~ v12_waybel_0(sK2,X18)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X18)))
      | ~ v3_orders_2(X18)
      | v1_waybel_7(sK2,X18) ) ),
    inference(global_subsumption,[],[f98,f4451])).

fof(f4451,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(sK4(X18,sK2),u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X19,sK4(X18,sK2)),sK2)
      | r2_hidden(X19,sK2)
      | ~ m1_subset_1(X19,u1_struct_0(sK0))
      | ~ v4_orders_2(X18)
      | ~ v5_orders_2(X18)
      | ~ v2_lattice3(X18)
      | ~ l1_orders_2(X18)
      | v1_xboole_0(sK2)
      | ~ v1_waybel_0(sK2,X18)
      | ~ v12_waybel_0(sK2,X18)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X18)))
      | ~ v3_orders_2(X18)
      | v1_waybel_7(sK2,X18) ) ),
    inference(resolution,[],[f1770,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1770,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK2)
      | r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f98,f99,f101,f102,f1766])).

fof(f1766,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_0(sK2,sK0)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK2)
      | r2_hidden(X0,sK2)
      | r2_hidden(X1,sK2)
      | ~ v1_waybel_7(sK2,sK0) ) ),
    inference(resolution,[],[f1562,f100])).

fof(f100,plain,(
    v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f1562,plain,(
    ! [X4,X5,X3] :
      ( ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
      | r2_hidden(X4,X3)
      | r2_hidden(X5,X3)
      | ~ v1_waybel_7(X3,sK0) ) ),
    inference(global_subsumption,[],[f110,f111,f114,f115,f1557])).

fof(f1557,plain,(
    ! [X4,X5,X3] :
      ( ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(X3)
      | ~ v1_waybel_0(X3,sK0)
      | ~ v12_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
      | r2_hidden(X4,X3)
      | r2_hidden(X5,X3)
      | ~ v1_waybel_7(X3,sK0) ) ),
    inference(resolution,[],[f137,f112])).

fof(f112,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f114,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f110,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,(
    v1_waybel_7(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    v1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f98,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f3156,plain,
    ( ~ spl11_219
    | ~ spl11_67
    | ~ spl11_242 ),
    inference(avatar_split_clause,[],[f3155,f1292,f470,f1190])).

fof(f470,plain,
    ( spl11_67
  <=> ~ l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_67])])).

fof(f1292,plain,
    ( spl11_242
  <=> ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ v1_waybel_0(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_242])])).

fof(f3155,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_242 ),
    inference(trivial_inequality_removal,[],[f3152])).

fof(f3152,plain,
    ( ~ l1_orders_2(sK0)
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_242 ),
    inference(resolution,[],[f1293,f99])).

fof(f1293,plain,
    ( ! [X0] :
        ( ~ v1_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl11_242 ),
    inference(avatar_component_clause,[],[f1292])).

fof(f3000,plain,
    ( ~ spl11_57
    | spl11_242
    | ~ spl11_219
    | spl11_7 ),
    inference(avatar_split_clause,[],[f2999,f182,f1190,f1292,f416])).

fof(f2999,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f2998,f379])).

fof(f2998,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v1_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f2997,f379])).

fof(f2997,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v1_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f2996,f1037])).

fof(f1037,plain,(
    u1_orders_2(sK0) = u1_orders_2(sK1) ),
    inference(equality_resolution,[],[f1027])).

fof(f1027,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_orders_2(sK1) = X1 ) ),
    inference(superposition,[],[f601,f380])).

fof(f601,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | u1_orders_2(sK1) = X1 ) ),
    inference(resolution,[],[f389,f152])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f389,plain,(
    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(global_subsumption,[],[f108,f382])).

fof(f382,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1) ),
    inference(superposition,[],[f118,f379])).

fof(f2996,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK1)
        | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v1_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_7 ),
    inference(resolution,[],[f183,f170])).

fof(f170,plain,(
    ! [X0,X3,X1] :
      ( v1_waybel_0(X3,X1)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_waybel_0(X3,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | ~ v1_waybel_0(X2,X0)
      | v1_waybel_0(X3,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_waybel_0(X3,X1)
                  | ~ v1_waybel_0(X2,X0)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_waybel_0(X3,X1)
                  | ~ v1_waybel_0(X2,X0)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v1_waybel_0(X2,X0)
                        & X2 = X3 )
                     => v1_waybel_0(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',t3_waybel_0)).

fof(f183,plain,
    ( ~ v1_waybel_0(sK2,sK1)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f182])).

fof(f1494,plain,
    ( ~ spl11_143
    | spl11_272
    | ~ spl11_5
    | ~ spl11_7
    | spl11_252
    | ~ spl11_57
    | ~ spl11_59
    | ~ spl11_61
    | ~ spl11_147
    | ~ spl11_219
    | spl11_3 ),
    inference(avatar_split_clause,[],[f1490,f176,f1190,f827,f428,f419,f416,f1401,f182,f179,f1492,f821])).

fof(f176,plain,
    ( spl11_3
  <=> ~ v1_waybel_7(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f1490,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | r2_hidden(k12_lattice3(sK1,sK4(sK1,sK2),sK5(sK1,sK2)),sK2)
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f1489,f379])).

fof(f1489,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(k12_lattice3(sK1,sK4(sK1,sK2),sK5(sK1,sK2)),sK2)
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(resolution,[],[f134,f177])).

fof(f177,plain,
    ( ~ v1_waybel_7(sK2,sK1)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f176])).

fof(f134,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1430,plain,
    ( ~ spl11_143
    | ~ spl11_5
    | ~ spl11_7
    | spl11_252
    | ~ spl11_57
    | ~ spl11_59
    | ~ spl11_61
    | ~ spl11_147
    | ~ spl11_219
    | spl11_260
    | spl11_3 ),
    inference(avatar_split_clause,[],[f1426,f176,f1428,f1190,f827,f428,f419,f416,f1401,f182,f179,f821])).

fof(f1426,plain,
    ( m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f1425,f379])).

fof(f1425,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f1424,f379])).

fof(f1424,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(resolution,[],[f138,f177])).

fof(f138,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1414,plain,(
    ~ spl11_252 ),
    inference(avatar_contradiction_clause,[],[f1407])).

fof(f1407,plain,
    ( $false
    | ~ spl11_252 ),
    inference(resolution,[],[f1402,f98])).

fof(f1402,plain,
    ( v1_xboole_0(sK2)
    | ~ spl11_252 ),
    inference(avatar_component_clause,[],[f1401])).

fof(f1406,plain,
    ( ~ spl11_143
    | ~ spl11_5
    | ~ spl11_7
    | spl11_252
    | ~ spl11_57
    | ~ spl11_59
    | ~ spl11_61
    | ~ spl11_147
    | ~ spl11_219
    | spl11_254
    | spl11_3 ),
    inference(avatar_split_clause,[],[f1399,f176,f1404,f1190,f827,f428,f419,f416,f1401,f182,f179,f821])).

fof(f1399,plain,
    ( m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f1398,f379])).

fof(f1398,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f1363,f379])).

fof(f1363,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(resolution,[],[f133,f177])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1397,plain,
    ( ~ spl11_219
    | ~ spl11_67
    | ~ spl11_216 ),
    inference(avatar_split_clause,[],[f1396,f1187,f470,f1190])).

fof(f1187,plain,
    ( spl11_216
  <=> ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ v12_waybel_0(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_216])])).

fof(f1396,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_216 ),
    inference(trivial_inequality_removal,[],[f1393])).

fof(f1393,plain,
    ( ~ l1_orders_2(sK0)
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_216 ),
    inference(resolution,[],[f1188,f100])).

fof(f1188,plain,
    ( ! [X0] :
        ( ~ v12_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl11_216 ),
    inference(avatar_component_clause,[],[f1187])).

fof(f1352,plain,
    ( spl11_50
    | spl11_250 ),
    inference(avatar_split_clause,[],[f1341,f1350,f1305])).

fof(f1305,plain,
    ( spl11_50
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f1341,plain,(
    ! [X4,X5] :
      ( k12_lattice3(sK0,X4,X5) = k2_yellow_0(sK0,k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1339])).

fof(f1339,plain,(
    ! [X4,X5] :
      ( k12_lattice3(sK0,X4,X5) = k2_yellow_0(sK0,k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f1108,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',redefinition_k7_domain_1)).

fof(f1108,plain,(
    ! [X2,X3] :
      ( k12_lattice3(sK0,X2,X3) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f110,f111,f114,f115,f1103])).

fof(f1103,plain,(
    ! [X2,X3] :
      ( ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k12_lattice3(sK0,X2,X3) = k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X2,X3)) ) ),
    inference(resolution,[],[f132,f112])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',t40_yellow_0)).

fof(f1315,plain,
    ( spl11_50
    | spl11_246 ),
    inference(avatar_split_clause,[],[f1301,f1313,f1305])).

fof(f1301,plain,(
    ! [X4,X5] :
      ( k12_lattice3(sK1,X4,X5) = k2_yellow_0(sK1,k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1297])).

fof(f1297,plain,(
    ! [X4,X5] :
      ( k12_lattice3(sK1,X4,X5) = k2_yellow_0(sK1,k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f1107,f158])).

fof(f1107,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK1,X0,X1) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f103,f104,f107,f108,f1106])).

fof(f1106,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK1,X0,X1) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1) ) ),
    inference(forward_demodulation,[],[f1105,f379])).

fof(f1105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | k12_lattice3(sK1,X0,X1) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) ) ),
    inference(forward_demodulation,[],[f1104,f379])).

fof(f1104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k12_lattice3(sK1,X0,X1) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) ) ),
    inference(forward_demodulation,[],[f1102,f379])).

fof(f1102,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v2_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k12_lattice3(sK1,X0,X1) = k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) ) ),
    inference(resolution,[],[f132,f105])).

fof(f104,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f1194,plain,(
    spl11_219 ),
    inference(avatar_contradiction_clause,[],[f1193])).

fof(f1193,plain,
    ( $false
    | ~ spl11_219 ),
    inference(resolution,[],[f1191,f102])).

fof(f1191,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_219 ),
    inference(avatar_component_clause,[],[f1190])).

fof(f1192,plain,
    ( ~ spl11_57
    | spl11_216
    | ~ spl11_219
    | spl11_5 ),
    inference(avatar_split_clause,[],[f1185,f179,f1190,f1187,f416])).

fof(f1185,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f1184,f379])).

fof(f1184,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v12_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f1183,f379])).

fof(f1183,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v12_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f1182,f1037])).

fof(f1182,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK1)
        | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v12_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_5 ),
    inference(resolution,[],[f168,f180])).

fof(f180,plain,
    ( ~ v12_waybel_0(sK2,sK1)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f179])).

fof(f168,plain,(
    ! [X0,X3,X1] :
      ( v12_waybel_0(X3,X1)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v12_waybel_0(X3,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | ~ v12_waybel_0(X2,X0)
      | v12_waybel_0(X3,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v13_waybel_0(X3,X1)
                      | ~ v13_waybel_0(X2,X0) )
                    & ( v12_waybel_0(X3,X1)
                      | ~ v12_waybel_0(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v13_waybel_0(X3,X1)
                      | ~ v13_waybel_0(X2,X0) )
                    & ( v12_waybel_0(X3,X1)
                      | ~ v12_waybel_0(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( ( v13_waybel_0(X2,X0)
                         => v13_waybel_0(X3,X1) )
                        & ( v12_waybel_0(X2,X0)
                         => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',t25_waybel_0)).

fof(f835,plain,(
    spl11_147 ),
    inference(avatar_contradiction_clause,[],[f834])).

fof(f834,plain,
    ( $false
    | ~ spl11_147 ),
    inference(resolution,[],[f828,f104])).

fof(f828,plain,
    ( ~ v4_orders_2(sK1)
    | ~ spl11_147 ),
    inference(avatar_component_clause,[],[f827])).

fof(f831,plain,(
    spl11_143 ),
    inference(avatar_contradiction_clause,[],[f830])).

fof(f830,plain,
    ( $false
    | ~ spl11_143 ),
    inference(resolution,[],[f822,f103])).

fof(f822,plain,
    ( ~ v3_orders_2(sK1)
    | ~ spl11_143 ),
    inference(avatar_component_clause,[],[f821])).

fof(f505,plain,(
    spl11_67 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl11_67 ),
    inference(resolution,[],[f471,f115])).

fof(f471,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_67 ),
    inference(avatar_component_clause,[],[f470])).

fof(f439,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl11_1 ),
    inference(resolution,[],[f381,f102])).

fof(f381,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_1 ),
    inference(backward_demodulation,[],[f379,f174])).

fof(f174,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl11_1
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f435,plain,(
    spl11_61 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl11_61 ),
    inference(resolution,[],[f429,f105])).

fof(f429,plain,
    ( ~ v5_orders_2(sK1)
    | ~ spl11_61 ),
    inference(avatar_component_clause,[],[f428])).

fof(f426,plain,(
    spl11_59 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl11_59 ),
    inference(resolution,[],[f420,f107])).

fof(f420,plain,
    ( ~ v2_lattice3(sK1)
    | ~ spl11_59 ),
    inference(avatar_component_clause,[],[f419])).

fof(f423,plain,(
    spl11_57 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl11_57 ),
    inference(resolution,[],[f417,f108])).

fof(f417,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl11_57 ),
    inference(avatar_component_clause,[],[f416])).

fof(f421,plain,
    ( ~ spl11_57
    | ~ spl11_59
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f414,f391,f419,f416])).

fof(f391,plain,
    ( spl11_46
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f414,plain,
    ( ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | ~ spl11_46 ),
    inference(resolution,[],[f392,f120])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',cc2_lattice3)).

fof(f392,plain,
    ( v2_struct_0(sK1)
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f391])).

fof(f413,plain,(
    spl11_49 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl11_49 ),
    inference(resolution,[],[f411,f108])).

fof(f411,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl11_49 ),
    inference(resolution,[],[f395,f117])).

fof(f117,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',dt_l1_orders_2)).

fof(f395,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl11_49 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl11_49
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f399,plain,
    ( spl11_46
    | ~ spl11_49
    | ~ spl11_51 ),
    inference(avatar_split_clause,[],[f383,f397,f394,f391])).

fof(f397,plain,
    ( spl11_51
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f383,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f126,f379])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t17_waybel_7.p',fc2_struct_0)).

fof(f184,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f171,f182,f179,f176,f173])).

fof(f171,plain,
    ( ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ v1_waybel_7(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_subsumption,[],[f98,f97])).

fof(f97,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1)
    | ~ v1_waybel_7(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
