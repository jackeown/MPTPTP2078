%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:51 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 260 expanded)
%              Number of leaves         :   21 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  366 (1459 expanded)
%              Number of equality atoms :   19 (  33 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f139,f202,f320,f346,f995,f1040,f1139])).

fof(f1139,plain,
    ( ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f1129])).

fof(f1129,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f1059,f1041,f84])).

fof(f84,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f1041,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f43,f305])).

fof(f305,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl7_3
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f1059,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f120,f305])).

fof(f120,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_1
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1040,plain,
    ( ~ spl7_2
    | spl7_4
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f1038])).

fof(f1038,plain,
    ( $false
    | ~ spl7_2
    | spl7_4
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f86,f1029,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1029,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2
    | spl7_4
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f66,f1024,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f1024,plain,
    ( r2_hidden(sK6(sK0,k1_xboole_0,sK5(u1_struct_0(sK0),sK1)),k1_xboole_0)
    | ~ spl7_2
    | spl7_4
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f49,f389,f1013,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f1013,plain,
    ( ~ r2_lattice3(sK0,k1_xboole_0,sK5(u1_struct_0(sK0),sK1))
    | ~ spl7_2
    | spl7_4
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f389,f398,f1011])).

fof(f1011,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f1009,f90])).

fof(f90,plain,(
    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f49,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f1009,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_18 ),
    inference(resolution,[],[f994,f92])).

fof(f92,plain,(
    r1_yellow_0(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f47,f48,f44,f49,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f994,plain,
    ( ! [X0,X1] :
        ( ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f993])).

fof(f993,plain,
    ( spl7_18
  <=> ! [X1,X0] :
        ( ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f398,plain,
    ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK5(u1_struct_0(sK0),sK1))
    | ~ spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f49,f42,f123,f136,f43,f322,f389,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f322,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f319,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f319,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl7_4
  <=> r1_tarski(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f136,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f91,f90])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f49,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f123,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl7_2
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f42,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f389,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f321,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f321,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f319,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f995,plain,
    ( spl7_18
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f133,f331,f993])).

fof(f331,plain,
    ( spl7_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ r1_yellow_0(sK0,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) ) ),
    inference(resolution,[],[f91,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f346,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f49,f333])).

fof(f333,plain,
    ( ~ l1_orders_2(sK0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f331])).

fof(f320,plain,
    ( spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f115,f317,f303])).

fof(f115,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f109,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f109,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f43,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f202,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f40,f124,f166,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f166,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl7_1 ),
    inference(backward_demodulation,[],[f136,f140])).

fof(f140,plain,
    ( sK1 = u1_struct_0(sK0)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f43,f119,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f119,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f124,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f40,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f139,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f39,f122,f118])).

fof(f39,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f125,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f38,f122,f118])).

fof(f38,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:40:07 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.51  % (32285)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (32296)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (32301)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (32281)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (32289)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (32275)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (32293)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (32283)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (32277)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (32297)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (32282)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (32299)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (32290)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (32280)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (32300)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (32298)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (32295)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (32278)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (32291)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (32291)Refutation not found, incomplete strategy% (32291)------------------------------
% 0.21/0.54  % (32291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32291)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32291)Memory used [KB]: 10746
% 0.21/0.54  % (32291)Time elapsed: 0.117 s
% 0.21/0.54  % (32291)------------------------------
% 0.21/0.54  % (32291)------------------------------
% 0.21/0.54  % (32303)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (32276)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (32302)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (32274)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (32284)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (32279)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (32288)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (32294)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (32287)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (32286)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (32300)Refutation not found, incomplete strategy% (32300)------------------------------
% 0.21/0.56  % (32300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32300)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32300)Memory used [KB]: 10874
% 0.21/0.56  % (32300)Time elapsed: 0.145 s
% 0.21/0.56  % (32300)------------------------------
% 0.21/0.56  % (32300)------------------------------
% 0.21/0.56  % (32292)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.77/0.61  % (32278)Refutation found. Thanks to Tanya!
% 1.77/0.61  % SZS status Theorem for theBenchmark
% 1.77/0.61  % SZS output start Proof for theBenchmark
% 1.77/0.61  fof(f1140,plain,(
% 1.77/0.61    $false),
% 1.77/0.61    inference(avatar_sat_refutation,[],[f125,f139,f202,f320,f346,f995,f1040,f1139])).
% 1.77/0.61  fof(f1139,plain,(
% 1.77/0.61    ~spl7_1 | ~spl7_3),
% 1.77/0.61    inference(avatar_contradiction_clause,[],[f1129])).
% 1.77/0.61  fof(f1129,plain,(
% 1.77/0.61    $false | (~spl7_1 | ~spl7_3)),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f1059,f1041,f84])).
% 1.77/0.61  fof(f84,plain,(
% 1.77/0.61    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.77/0.61    inference(equality_resolution,[],[f56])).
% 1.77/0.61  fof(f56,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f27])).
% 1.77/0.61  fof(f27,plain,(
% 1.77/0.61    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.77/0.61    inference(ennf_transformation,[],[f15])).
% 1.77/0.61  fof(f15,axiom,(
% 1.77/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.77/0.61  fof(f1041,plain,(
% 1.77/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl7_3),
% 1.77/0.61    inference(backward_demodulation,[],[f43,f305])).
% 1.77/0.61  fof(f305,plain,(
% 1.77/0.61    sK1 = u1_struct_0(sK0) | ~spl7_3),
% 1.77/0.61    inference(avatar_component_clause,[],[f303])).
% 1.77/0.61  fof(f303,plain,(
% 1.77/0.61    spl7_3 <=> sK1 = u1_struct_0(sK0)),
% 1.77/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.77/0.61  fof(f43,plain,(
% 1.77/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  fof(f19,plain,(
% 1.77/0.61    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.77/0.61    inference(flattening,[],[f18])).
% 1.77/0.61  fof(f18,plain,(
% 1.77/0.61    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.77/0.61    inference(ennf_transformation,[],[f17])).
% 1.77/0.61  fof(f17,negated_conjecture,(
% 1.77/0.61    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.77/0.61    inference(negated_conjecture,[],[f16])).
% 1.77/0.61  fof(f16,conjecture,(
% 1.77/0.61    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.77/0.61  fof(f1059,plain,(
% 1.77/0.61    v1_subset_1(sK1,sK1) | (~spl7_1 | ~spl7_3)),
% 1.77/0.61    inference(backward_demodulation,[],[f120,f305])).
% 1.77/0.61  fof(f120,plain,(
% 1.77/0.61    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl7_1),
% 1.77/0.61    inference(avatar_component_clause,[],[f118])).
% 1.77/0.61  fof(f118,plain,(
% 1.77/0.61    spl7_1 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.77/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.77/0.61  fof(f1040,plain,(
% 1.77/0.61    ~spl7_2 | spl7_4 | ~spl7_18),
% 1.77/0.61    inference(avatar_contradiction_clause,[],[f1038])).
% 1.77/0.61  fof(f1038,plain,(
% 1.77/0.61    $false | (~spl7_2 | spl7_4 | ~spl7_18)),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f86,f1029,f57])).
% 1.77/0.61  fof(f57,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.77/0.61    inference(cnf_transformation,[],[f6])).
% 1.77/0.61  fof(f6,axiom,(
% 1.77/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.77/0.61  fof(f1029,plain,(
% 1.77/0.61    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl7_2 | spl7_4 | ~spl7_18)),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f66,f1024,f50])).
% 1.77/0.61  fof(f50,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f20])).
% 1.77/0.61  fof(f20,plain,(
% 1.77/0.61    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.77/0.61    inference(ennf_transformation,[],[f8])).
% 1.77/0.61  fof(f8,axiom,(
% 1.77/0.61    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.77/0.61  fof(f1024,plain,(
% 1.77/0.61    r2_hidden(sK6(sK0,k1_xboole_0,sK5(u1_struct_0(sK0),sK1)),k1_xboole_0) | (~spl7_2 | spl7_4 | ~spl7_18)),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f49,f389,f1013,f82])).
% 1.77/0.61  fof(f82,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK6(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f37])).
% 1.77/0.61  fof(f37,plain,(
% 1.77/0.61    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.77/0.61    inference(flattening,[],[f36])).
% 1.77/0.61  fof(f36,plain,(
% 1.77/0.61    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.77/0.61    inference(ennf_transformation,[],[f9])).
% 1.77/0.61  fof(f9,axiom,(
% 1.77/0.61    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 1.77/0.61  fof(f1013,plain,(
% 1.77/0.61    ~r2_lattice3(sK0,k1_xboole_0,sK5(u1_struct_0(sK0),sK1)) | (~spl7_2 | spl7_4 | ~spl7_18)),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f389,f398,f1011])).
% 1.77/0.61  fof(f1011,plain,(
% 1.77/0.61    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_18),
% 1.77/0.61    inference(forward_demodulation,[],[f1009,f90])).
% 1.77/0.61  fof(f90,plain,(
% 1.77/0.61    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f49,f54])).
% 1.77/0.61  fof(f54,plain,(
% 1.77/0.61    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f26])).
% 1.77/0.61  fof(f26,plain,(
% 1.77/0.61    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.77/0.61    inference(ennf_transformation,[],[f10])).
% 1.77/0.61  fof(f10,axiom,(
% 1.77/0.61    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.77/0.61  fof(f1009,plain,(
% 1.77/0.61    ( ! [X0] : (r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_18),
% 1.77/0.61    inference(resolution,[],[f994,f92])).
% 1.77/0.61  fof(f92,plain,(
% 1.77/0.61    r1_yellow_0(sK0,k1_xboole_0)),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f47,f48,f44,f49,f67])).
% 1.77/0.61  fof(f67,plain,(
% 1.77/0.61    ( ! [X0] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,k1_xboole_0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f32])).
% 1.77/0.61  fof(f32,plain,(
% 1.77/0.61    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.77/0.61    inference(flattening,[],[f31])).
% 1.77/0.61  fof(f31,plain,(
% 1.77/0.61    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.77/0.61    inference(ennf_transformation,[],[f13])).
% 1.77/0.61  fof(f13,axiom,(
% 1.77/0.61    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 1.77/0.61  fof(f44,plain,(
% 1.77/0.61    ~v2_struct_0(sK0)),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  fof(f48,plain,(
% 1.77/0.61    v1_yellow_0(sK0)),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  fof(f47,plain,(
% 1.77/0.61    v5_orders_2(sK0)),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  fof(f994,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) | ~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_18),
% 1.77/0.61    inference(avatar_component_clause,[],[f993])).
% 1.77/0.61  fof(f993,plain,(
% 1.77/0.61    spl7_18 <=> ! [X1,X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) | ~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.77/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.77/0.61  fof(f398,plain,(
% 1.77/0.61    ~r1_orders_2(sK0,k3_yellow_0(sK0),sK5(u1_struct_0(sK0),sK1)) | (~spl7_2 | spl7_4)),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f49,f42,f123,f136,f43,f322,f389,f64])).
% 1.77/0.61  fof(f64,plain,(
% 1.77/0.61    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f30])).
% 1.77/0.61  fof(f30,plain,(
% 1.77/0.61    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.77/0.61    inference(flattening,[],[f29])).
% 1.77/0.61  fof(f29,plain,(
% 1.77/0.61    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.77/0.61    inference(ennf_transformation,[],[f14])).
% 1.77/0.61  fof(f14,axiom,(
% 1.77/0.61    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.77/0.61  fof(f322,plain,(
% 1.77/0.61    ~r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1) | spl7_4),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f319,f79])).
% 1.77/0.61  fof(f79,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f35])).
% 1.77/0.61  fof(f35,plain,(
% 1.77/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.77/0.61    inference(ennf_transformation,[],[f1])).
% 1.77/0.61  fof(f1,axiom,(
% 1.77/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.77/0.61  fof(f319,plain,(
% 1.77/0.61    ~r1_tarski(u1_struct_0(sK0),sK1) | spl7_4),
% 1.77/0.61    inference(avatar_component_clause,[],[f317])).
% 1.77/0.61  fof(f317,plain,(
% 1.77/0.61    spl7_4 <=> r1_tarski(u1_struct_0(sK0),sK1)),
% 1.77/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.77/0.61  fof(f136,plain,(
% 1.77/0.61    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.77/0.61    inference(superposition,[],[f91,f90])).
% 1.77/0.61  fof(f91,plain,(
% 1.77/0.61    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))) )),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f49,f59])).
% 1.77/0.61  fof(f59,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 1.77/0.61    inference(cnf_transformation,[],[f28])).
% 1.77/0.61  fof(f28,plain,(
% 1.77/0.61    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.77/0.61    inference(ennf_transformation,[],[f12])).
% 1.77/0.61  fof(f12,axiom,(
% 1.77/0.61    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 1.77/0.61  fof(f123,plain,(
% 1.77/0.61    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl7_2),
% 1.77/0.61    inference(avatar_component_clause,[],[f122])).
% 1.77/0.61  fof(f122,plain,(
% 1.77/0.61    spl7_2 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.77/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.77/0.61  fof(f42,plain,(
% 1.77/0.61    v13_waybel_0(sK1,sK0)),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  fof(f389,plain,(
% 1.77/0.61    m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl7_4),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f321,f53])).
% 1.77/0.61  fof(f53,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f25])).
% 1.77/0.61  fof(f25,plain,(
% 1.77/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.77/0.61    inference(ennf_transformation,[],[f4])).
% 1.77/0.61  fof(f4,axiom,(
% 1.77/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.77/0.61  fof(f321,plain,(
% 1.77/0.61    r2_hidden(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl7_4),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f319,f78])).
% 1.77/0.61  fof(f78,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f35])).
% 1.77/0.61  fof(f49,plain,(
% 1.77/0.61    l1_orders_2(sK0)),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  fof(f66,plain,(
% 1.77/0.61    v1_xboole_0(k1_xboole_0)),
% 1.77/0.61    inference(cnf_transformation,[],[f2])).
% 1.77/0.61  fof(f2,axiom,(
% 1.77/0.61    v1_xboole_0(k1_xboole_0)),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.77/0.61  fof(f86,plain,(
% 1.77/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.77/0.61    inference(equality_resolution,[],[f69])).
% 1.77/0.61  fof(f69,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.77/0.61    inference(cnf_transformation,[],[f3])).
% 1.77/0.61  fof(f3,axiom,(
% 1.77/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.77/0.61  fof(f995,plain,(
% 1.77/0.61    spl7_18 | ~spl7_6),
% 1.77/0.61    inference(avatar_split_clause,[],[f133,f331,f993])).
% 1.77/0.61  fof(f331,plain,(
% 1.77/0.61    spl7_6 <=> l1_orders_2(sK0)),
% 1.77/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.77/0.61  fof(f133,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) )),
% 1.77/0.61    inference(resolution,[],[f91,f88])).
% 1.77/0.61  fof(f88,plain,(
% 1.77/0.61    ( ! [X0,X3,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)) )),
% 1.77/0.61    inference(equality_resolution,[],[f75])).
% 1.77/0.61  fof(f75,plain,(
% 1.77/0.61    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 1.77/0.61    inference(cnf_transformation,[],[f34])).
% 1.77/0.61  fof(f34,plain,(
% 1.77/0.61    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.77/0.61    inference(flattening,[],[f33])).
% 1.77/0.61  fof(f33,plain,(
% 1.77/0.61    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.77/0.61    inference(ennf_transformation,[],[f11])).
% 1.77/0.61  fof(f11,axiom,(
% 1.77/0.61    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 1.77/0.61  fof(f346,plain,(
% 1.77/0.61    spl7_6),
% 1.77/0.61    inference(avatar_contradiction_clause,[],[f343])).
% 1.77/0.61  fof(f343,plain,(
% 1.77/0.61    $false | spl7_6),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f49,f333])).
% 1.77/0.61  fof(f333,plain,(
% 1.77/0.61    ~l1_orders_2(sK0) | spl7_6),
% 1.77/0.61    inference(avatar_component_clause,[],[f331])).
% 1.77/0.61  fof(f320,plain,(
% 1.77/0.61    spl7_3 | ~spl7_4),
% 1.77/0.61    inference(avatar_split_clause,[],[f115,f317,f303])).
% 1.77/0.61  fof(f115,plain,(
% 1.77/0.61    ~r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 1.77/0.61    inference(resolution,[],[f109,f71])).
% 1.77/0.61  fof(f71,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.77/0.61    inference(cnf_transformation,[],[f3])).
% 1.77/0.61  fof(f109,plain,(
% 1.77/0.61    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f43,f58])).
% 1.77/0.61  fof(f58,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f6])).
% 1.77/0.61  fof(f202,plain,(
% 1.77/0.61    spl7_1 | spl7_2),
% 1.77/0.61    inference(avatar_contradiction_clause,[],[f197])).
% 1.77/0.61  fof(f197,plain,(
% 1.77/0.61    $false | (spl7_1 | spl7_2)),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f40,f124,f166,f52])).
% 1.77/0.61  fof(f52,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f24])).
% 1.77/0.61  fof(f24,plain,(
% 1.77/0.61    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.77/0.61    inference(flattening,[],[f23])).
% 1.77/0.61  fof(f23,plain,(
% 1.77/0.61    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.77/0.61    inference(ennf_transformation,[],[f5])).
% 1.77/0.61  fof(f5,axiom,(
% 1.77/0.61    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.77/0.61  fof(f166,plain,(
% 1.77/0.61    m1_subset_1(k3_yellow_0(sK0),sK1) | spl7_1),
% 1.77/0.61    inference(backward_demodulation,[],[f136,f140])).
% 1.77/0.61  fof(f140,plain,(
% 1.77/0.61    sK1 = u1_struct_0(sK0) | spl7_1),
% 1.77/0.61    inference(unit_resulting_resolution,[],[f43,f119,f55])).
% 1.77/0.61  fof(f55,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f27])).
% 1.77/0.61  fof(f119,plain,(
% 1.77/0.61    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl7_1),
% 1.77/0.61    inference(avatar_component_clause,[],[f118])).
% 1.77/0.61  fof(f124,plain,(
% 1.77/0.61    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl7_2),
% 1.77/0.61    inference(avatar_component_clause,[],[f122])).
% 1.77/0.61  fof(f40,plain,(
% 1.77/0.61    ~v1_xboole_0(sK1)),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  fof(f139,plain,(
% 1.77/0.61    ~spl7_1 | spl7_2),
% 1.77/0.61    inference(avatar_split_clause,[],[f39,f122,f118])).
% 1.77/0.61  fof(f39,plain,(
% 1.77/0.61    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  fof(f125,plain,(
% 1.77/0.61    spl7_1 | ~spl7_2),
% 1.77/0.61    inference(avatar_split_clause,[],[f38,f122,f118])).
% 1.77/0.61  fof(f38,plain,(
% 1.77/0.61    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  % SZS output end Proof for theBenchmark
% 1.77/0.61  % (32278)------------------------------
% 1.77/0.61  % (32278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.61  % (32278)Termination reason: Refutation
% 1.77/0.61  
% 1.77/0.61  % (32278)Memory used [KB]: 6780
% 1.77/0.61  % (32278)Time elapsed: 0.184 s
% 1.77/0.61  % (32278)------------------------------
% 1.77/0.61  % (32278)------------------------------
% 1.77/0.62  % (32273)Success in time 0.241 s
%------------------------------------------------------------------------------
