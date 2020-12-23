%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t9_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:08 EDT 2019

% Result     : Theorem 15.08s
% Output     : Refutation 15.08s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 349 expanded)
%              Number of leaves         :   22 ( 102 expanded)
%              Depth                    :   23
%              Number of atoms          :  497 ( 987 expanded)
%              Number of equality atoms :  120 ( 258 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15724,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f231,f189,f149,f14452,f386])).

fof(f386,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2 ) ),
    inference(forward_demodulation,[],[f385,f230])).

fof(f230,plain,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k1_zfmisc_1(X0) ),
    inference(forward_demodulation,[],[f158,f157])).

fof(f157,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',redefinition_k9_setfam_1)).

fof(f158,plain,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',t4_waybel_7)).

fof(f385,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2 ) ),
    inference(forward_demodulation,[],[f384,f230])).

fof(f384,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2 ) ),
    inference(subsumption_resolution,[],[f383,f162])).

fof(f162,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',fc7_yellow_1)).

fof(f383,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f382,f163])).

fof(f163,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

fof(f382,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v4_orders_2(k3_yellow_1(X0))
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f381,f164])).

fof(f164,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

fof(f381,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v5_orders_2(k3_yellow_1(X0))
      | ~ v4_orders_2(k3_yellow_1(X0))
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f380,f274])).

fof(f274,plain,(
    ! [X0] : v1_lattice3(k3_yellow_1(X0)) ),
    inference(subsumption_resolution,[],[f273,f168])).

fof(f168,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',dt_k3_yellow_1)).

fof(f273,plain,(
    ! [X0] :
      ( v1_lattice3(k3_yellow_1(X0))
      | ~ l1_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f272,f160])).

fof(f160,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

fof(f272,plain,(
    ! [X0] :
      ( v1_lattice3(k3_yellow_1(X0))
      | v2_struct_0(k3_yellow_1(X0))
      | ~ l1_orders_2(k3_yellow_1(X0)) ) ),
    inference(resolution,[],[f177,f166])).

fof(f166,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',fc1_waybel_7)).

fof(f177,plain,(
    ! [X0] :
      ( ~ v11_waybel_1(X0)
      | v1_lattice3(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f71])).

fof(f71,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',cc8_waybel_1)).

fof(f380,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v1_lattice3(k3_yellow_1(X0))
      | ~ v5_orders_2(k3_yellow_1(X0))
      | ~ v4_orders_2(k3_yellow_1(X0))
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f379,f277])).

fof(f277,plain,(
    ! [X0] : v2_lattice3(k3_yellow_1(X0)) ),
    inference(subsumption_resolution,[],[f276,f168])).

fof(f276,plain,(
    ! [X0] :
      ( v2_lattice3(k3_yellow_1(X0))
      | ~ l1_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f275,f160])).

fof(f275,plain,(
    ! [X0] :
      ( v2_lattice3(k3_yellow_1(X0))
      | v2_struct_0(k3_yellow_1(X0))
      | ~ l1_orders_2(k3_yellow_1(X0)) ) ),
    inference(resolution,[],[f178,f166])).

fof(f178,plain,(
    ! [X0] :
      ( ~ v11_waybel_1(X0)
      | v2_lattice3(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f379,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v2_lattice3(k3_yellow_1(X0))
      | ~ v1_lattice3(k3_yellow_1(X0))
      | ~ v5_orders_2(k3_yellow_1(X0))
      | ~ v4_orders_2(k3_yellow_1(X0))
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f378,f168])).

fof(f378,plain,(
    ! [X2,X0,X1] :
      ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ l1_orders_2(k3_yellow_1(X0))
      | k7_waybel_1(k3_yellow_1(X0),X1) = X2
      | ~ v2_lattice3(k3_yellow_1(X0))
      | ~ v1_lattice3(k3_yellow_1(X0))
      | ~ v5_orders_2(k3_yellow_1(X0))
      | ~ v4_orders_2(k3_yellow_1(X0))
      | ~ v3_orders_2(k3_yellow_1(X0)) ) ),
    inference(resolution,[],[f183,f166])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ v11_waybel_1(X0)
      | ~ r6_waybel_1(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k7_waybel_1(X0,X1) = X2
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f142])).

fof(f142,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r6_waybel_1(X0,X1,X2)
                  | k7_waybel_1(X0,X1) != X2 )
                & ( k7_waybel_1(X0,X1) = X2
                  | ~ r6_waybel_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> k7_waybel_1(X0,X1) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> k7_waybel_1(X0,X1) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v11_waybel_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r6_waybel_1(X0,X1,X2)
              <=> k7_waybel_1(X0,X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',t11_yellow_5)).

fof(f14452,plain,(
    r6_waybel_1(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f14447,f303])).

fof(f303,plain,(
    k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) = sK0 ),
    inference(resolution,[],[f234,f266])).

fof(f266,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f212,f231])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f61])).

fof(f61,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',t3_subset)).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1 ) ),
    inference(forward_demodulation,[],[f195,f192])).

fof(f192,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',redefinition_k6_subset_1)).

fof(f195,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f62])).

fof(f62,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',t45_xboole_1)).

fof(f14447,plain,
    ( k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) != sK0
    | r6_waybel_1(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f14446])).

fof(f14446,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) != sK0
    | r6_waybel_1(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f12060,f455])).

fof(f455,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k6_subset_1(X1,X0)) = k1_xboole_0 ),
    inference(resolution,[],[f243,f210])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',d7_xboole_0)).

fof(f243,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(resolution,[],[f198,f233])).

fof(f233,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(forward_demodulation,[],[f188,f192])).

fof(f188,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',t79_xboole_1)).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',symmetry_r1_xboole_0)).

fof(f12060,plain,(
    ! [X0] :
      ( k3_xboole_0(sK1,k6_subset_1(sK0,X0)) != k1_xboole_0
      | k2_xboole_0(sK1,k6_subset_1(sK0,X0)) != sK0
      | r6_waybel_1(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X0)) ) ),
    inference(backward_demodulation,[],[f11992,f10333])).

fof(f10333,plain,(
    ! [X0] :
      ( k2_xboole_0(sK1,k6_subset_1(sK0,X0)) != sK0
      | k11_lattice3(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X0)) != k1_xboole_0
      | r6_waybel_1(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X0)) ) ),
    inference(backward_demodulation,[],[f10331,f921])).

fof(f921,plain,(
    ! [X0] :
      ( k10_lattice3(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X0)) != sK0
      | k11_lattice3(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X0)) != k1_xboole_0
      | r6_waybel_1(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X0)) ) ),
    inference(resolution,[],[f840,f189])).

fof(f840,plain,(
    ! [X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(sK0))
      | k10_lattice3(k3_yellow_1(sK0),sK1,X19) != sK0
      | k11_lattice3(k3_yellow_1(sK0),sK1,X19) != k1_xboole_0
      | r6_waybel_1(k3_yellow_1(sK0),sK1,X19) ) ),
    inference(resolution,[],[f367,f231])).

fof(f367,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | k10_lattice3(k3_yellow_1(X2),X3,X4) != X2
      | k11_lattice3(k3_yellow_1(X2),X3,X4) != k1_xboole_0
      | r6_waybel_1(k3_yellow_1(X2),X3,X4) ) ),
    inference(forward_demodulation,[],[f366,f230])).

fof(f366,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | k10_lattice3(k3_yellow_1(X2),X3,X4) != X2
      | k11_lattice3(k3_yellow_1(X2),X3,X4) != k1_xboole_0
      | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))
      | r6_waybel_1(k3_yellow_1(X2),X3,X4) ) ),
    inference(forward_demodulation,[],[f365,f230])).

fof(f365,plain,(
    ! [X4,X2,X3] :
      ( k10_lattice3(k3_yellow_1(X2),X3,X4) != X2
      | k11_lattice3(k3_yellow_1(X2),X3,X4) != k1_xboole_0
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X2)))
      | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))
      | r6_waybel_1(k3_yellow_1(X2),X3,X4) ) ),
    inference(forward_demodulation,[],[f364,f153])).

fof(f153,plain,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',t19_yellow_1)).

fof(f364,plain,(
    ! [X4,X2,X3] :
      ( k11_lattice3(k3_yellow_1(X2),X3,X4) != k1_xboole_0
      | k10_lattice3(k3_yellow_1(X2),X3,X4) != k4_yellow_0(k3_yellow_1(X2))
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X2)))
      | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))
      | r6_waybel_1(k3_yellow_1(X2),X3,X4) ) ),
    inference(forward_demodulation,[],[f363,f155])).

fof(f155,plain,(
    ! [X0] : k3_yellow_0(k3_yellow_1(X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0] : k3_yellow_0(k3_yellow_1(X0)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',t18_yellow_1)).

fof(f363,plain,(
    ! [X4,X2,X3] :
      ( k11_lattice3(k3_yellow_1(X2),X3,X4) != k3_yellow_0(k3_yellow_1(X2))
      | k10_lattice3(k3_yellow_1(X2),X3,X4) != k4_yellow_0(k3_yellow_1(X2))
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X2)))
      | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))
      | r6_waybel_1(k3_yellow_1(X2),X3,X4) ) ),
    inference(subsumption_resolution,[],[f362,f160])).

fof(f362,plain,(
    ! [X4,X2,X3] :
      ( k11_lattice3(k3_yellow_1(X2),X3,X4) != k3_yellow_0(k3_yellow_1(X2))
      | k10_lattice3(k3_yellow_1(X2),X3,X4) != k4_yellow_0(k3_yellow_1(X2))
      | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(X2)))
      | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))
      | r6_waybel_1(k3_yellow_1(X2),X3,X4)
      | v2_struct_0(k3_yellow_1(X2)) ) ),
    inference(resolution,[],[f182,f168])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | k11_lattice3(X0,X1,X2) != k3_yellow_0(X0)
      | k10_lattice3(X0,X1,X2) != k4_yellow_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r6_waybel_1(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r6_waybel_1(X0,X1,X2)
                  | k11_lattice3(X0,X1,X2) != k3_yellow_0(X0)
                  | k10_lattice3(X0,X1,X2) != k4_yellow_0(X0) )
                & ( ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                    & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) )
                  | ~ r6_waybel_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f140])).

fof(f140,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r6_waybel_1(X0,X1,X2)
                  | k11_lattice3(X0,X1,X2) != k3_yellow_0(X0)
                  | k10_lattice3(X0,X1,X2) != k4_yellow_0(X0) )
                & ( ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                    & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) )
                  | ~ r6_waybel_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                  & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                  & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r6_waybel_1(X0,X1,X2)
              <=> ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                  & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',d23_waybel_1)).

fof(f10331,plain,(
    ! [X3] : k2_xboole_0(sK1,k6_subset_1(sK0,X3)) = k10_lattice3(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X3)) ),
    inference(forward_demodulation,[],[f9625,f391])).

fof(f391,plain,(
    ! [X0] : k13_lattice3(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X0)) = k2_xboole_0(sK1,k6_subset_1(sK0,X0)) ),
    inference(resolution,[],[f344,f189])).

fof(f344,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
      | k13_lattice3(k3_yellow_1(sK0),sK1,X5) = k2_xboole_0(sK1,X5) ) ),
    inference(resolution,[],[f238,f231])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(forward_demodulation,[],[f237,f230])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(forward_demodulation,[],[f200,f230])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',t17_yellow_1)).

fof(f9625,plain,(
    ! [X3] : k13_lattice3(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X3)) = k10_lattice3(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X3)) ),
    inference(resolution,[],[f3041,f189])).

fof(f3041,plain,(
    ! [X63] :
      ( ~ m1_subset_1(X63,k1_zfmisc_1(sK0))
      | k13_lattice3(k3_yellow_1(sK0),sK1,X63) = k10_lattice3(k3_yellow_1(sK0),sK1,X63) ) ),
    inference(resolution,[],[f401,f231])).

fof(f401,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k13_lattice3(k3_yellow_1(X1),X2,X0) = k10_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f400,f230])).

fof(f400,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k13_lattice3(k3_yellow_1(X1),X2,X0) = k10_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f399,f230])).

fof(f399,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k13_lattice3(k3_yellow_1(X1),X2,X0) = k10_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(subsumption_resolution,[],[f398,f164])).

fof(f398,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k13_lattice3(k3_yellow_1(X1),X2,X0) = k10_lattice3(k3_yellow_1(X1),X2,X0)
      | ~ v5_orders_2(k3_yellow_1(X1)) ) ),
    inference(subsumption_resolution,[],[f395,f168])).

fof(f395,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ l1_orders_2(k3_yellow_1(X1))
      | k13_lattice3(k3_yellow_1(X1),X2,X0) = k10_lattice3(k3_yellow_1(X1),X2,X0)
      | ~ v5_orders_2(k3_yellow_1(X1)) ) ),
    inference(resolution,[],[f274,f221])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f125])).

fof(f125,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',redefinition_k13_lattice3)).

fof(f11992,plain,(
    ! [X3] : k3_xboole_0(sK1,k6_subset_1(sK0,X3)) = k11_lattice3(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X3)) ),
    inference(forward_demodulation,[],[f11292,f387])).

fof(f387,plain,(
    ! [X0] : k12_lattice3(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X0)) = k3_xboole_0(sK1,k6_subset_1(sK0,X0)) ),
    inference(resolution,[],[f340,f189])).

fof(f340,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
      | k12_lattice3(k3_yellow_1(sK0),sK1,X5) = k3_xboole_0(sK1,X5) ) ),
    inference(resolution,[],[f236,f231])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(forward_demodulation,[],[f235,f230])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(forward_demodulation,[],[f201,f230])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f11292,plain,(
    ! [X3] : k12_lattice3(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X3)) = k11_lattice3(k3_yellow_1(sK0),sK1,k6_subset_1(sK0,X3)) ),
    inference(resolution,[],[f3113,f189])).

fof(f3113,plain,(
    ! [X63] :
      ( ~ m1_subset_1(X63,k1_zfmisc_1(sK0))
      | k12_lattice3(k3_yellow_1(sK0),sK1,X63) = k11_lattice3(k3_yellow_1(sK0),sK1,X63) ) ),
    inference(resolution,[],[f417,f231])).

fof(f417,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k12_lattice3(k3_yellow_1(X1),X2,X0) = k11_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f416,f230])).

fof(f416,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k12_lattice3(k3_yellow_1(X1),X2,X0) = k11_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f415,f230])).

fof(f415,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k12_lattice3(k3_yellow_1(X1),X2,X0) = k11_lattice3(k3_yellow_1(X1),X2,X0) ) ),
    inference(subsumption_resolution,[],[f414,f164])).

fof(f414,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k12_lattice3(k3_yellow_1(X1),X2,X0) = k11_lattice3(k3_yellow_1(X1),X2,X0)
      | ~ v5_orders_2(k3_yellow_1(X1)) ) ),
    inference(subsumption_resolution,[],[f411,f168])).

fof(f411,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ l1_orders_2(k3_yellow_1(X1))
      | k12_lattice3(k3_yellow_1(X1),X2,X0) = k11_lattice3(k3_yellow_1(X1),X2,X0)
      | ~ v5_orders_2(k3_yellow_1(X1)) ) ),
    inference(resolution,[],[f277,f220])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f123])).

fof(f123,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',redefinition_k12_lattice3)).

fof(f149,plain,(
    k7_waybel_1(k3_yellow_1(sK0),sK1) != k6_subset_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f139])).

fof(f139,plain,
    ( k7_waybel_1(k3_yellow_1(sK0),sK1) != k6_subset_1(sK0,sK1)
    & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f82,f138])).

fof(f138,plain,
    ( ? [X0,X1] :
        ( k7_waybel_1(k3_yellow_1(X0),X1) != k6_subset_1(X0,X1)
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( k7_waybel_1(k3_yellow_1(sK0),sK1) != k6_subset_1(sK0,sK1)
      & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ? [X0,X1] :
      ( k7_waybel_1(k3_yellow_1(X0),X1) != k6_subset_1(X0,X1)
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => k7_waybel_1(k3_yellow_1(X0),X1) = k6_subset_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => k7_waybel_1(k3_yellow_1(X0),X1) = k6_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',t9_waybel_7)).

fof(f189,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t9_waybel_7.p',dt_k6_subset_1)).

fof(f231,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f148,f230])).

fof(f148,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f139])).
%------------------------------------------------------------------------------
