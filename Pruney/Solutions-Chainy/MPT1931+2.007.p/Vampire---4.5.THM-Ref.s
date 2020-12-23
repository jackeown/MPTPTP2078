%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 233 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   25
%              Number of atoms          :  265 (1072 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f334,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f333])).

fof(f333,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f331,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f331,plain,
    ( v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f330,f95])).

fof(f95,plain,(
    m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f94,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f94,plain,
    ( v2_struct_0(sK1)
    | m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f83,f50])).

fof(f50,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f48,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f48,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f46,f32])).

fof(f32,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1) ),
    inference(resolution,[],[f34,f29])).

fof(f29,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f83,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) ),
    inference(resolution,[],[f43,f51])).

fof(f51,plain,(
    l1_waybel_0(sK2(sK1),sK1) ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | l1_waybel_0(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_waybel_0)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(f330,plain,
    ( ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f329,f29])).

fof(f329,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f328,f26])).

fof(f328,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f327,f32])).

fof(f327,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f326,f30])).

fof(f30,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f326,plain,
    ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,
    ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | spl5_2 ),
    inference(resolution,[],[f324,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f324,plain,
    ( ! [X0] :
        ( r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),u1_struct_0(sK0))
        | r1_waybel_0(sK0,sK1,X0) )
    | spl5_2 ),
    inference(subsumption_resolution,[],[f323,f112])).

fof(f112,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f323,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,X0)
      | v1_xboole_0(u1_struct_0(sK0))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f274,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f274,plain,(
    ! [X2] :
      ( m1_subset_1(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X2,k4_yellow_6(sK1,sK2(sK1)))),u1_struct_0(sK0))
      | r1_waybel_0(sK0,sK1,X2) ) ),
    inference(resolution,[],[f272,f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(k2_waybel_0(sK0,sK1,X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f149,f31])).

fof(f149,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(k2_waybel_0(sK0,sK1,X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f148,f26])).

fof(f148,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(k2_waybel_0(sK0,sK1,X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f138,f32])).

fof(f138,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(k2_waybel_0(sK0,sK1,X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

fof(f272,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f196,f95])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK4(sK0,sK1,X1,X0),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f195,f31])).

fof(f195,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK4(sK0,sK1,X1,X0),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f194,f26])).

fof(f194,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK4(sK0,sK1,X1,X0),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f183,f32])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK4(sK0,sK1,X1,X0),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(resolution,[],[f37,f29])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f118,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f116,f31])).

fof(f116,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f115,f32])).

fof(f115,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f113,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f113,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (14576)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.42  % (14576)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f334,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f118,f333])).
% 0.21/0.42  fof(f333,plain,(
% 0.21/0.42    spl5_2),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f332])).
% 0.21/0.42  fof(f332,plain,(
% 0.21/0.42    $false | spl5_2),
% 0.21/0.42    inference(subsumption_resolution,[],[f331,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ~v2_struct_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,negated_conjecture,(
% 0.21/0.42    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.42    inference(negated_conjecture,[],[f9])).
% 0.21/0.42  fof(f9,conjecture,(
% 0.21/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.21/0.42  fof(f331,plain,(
% 0.21/0.42    v2_struct_0(sK0) | spl5_2),
% 0.21/0.42    inference(subsumption_resolution,[],[f330,f95])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))),
% 0.21/0.42    inference(subsumption_resolution,[],[f94,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ~v2_struct_0(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    v2_struct_0(sK1) | m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))),
% 0.21/0.42    inference(subsumption_resolution,[],[f83,f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    l1_struct_0(sK1)),
% 0.21/0.42    inference(resolution,[],[f48,f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    l1_orders_2(sK1)),
% 0.21/0.42    inference(subsumption_resolution,[],[f46,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    l1_struct_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ~l1_struct_0(sK0) | l1_orders_2(sK1)),
% 0.21/0.42    inference(resolution,[],[f34,f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    l1_waybel_0(sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_orders_2(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    ~l1_struct_0(sK1) | v2_struct_0(sK1) | m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))),
% 0.21/0.42    inference(resolution,[],[f43,f51])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    l1_waybel_0(sK2(sK1),sK1)),
% 0.21/0.42    inference(resolution,[],[f50,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0] : (~l1_struct_0(X0) | l1_waybel_0(sK2(X0),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) => ? [X1] : l1_waybel_0(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_waybel_0)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0) | m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).
% 0.21/0.42  fof(f330,plain,(
% 0.21/0.42    ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | spl5_2),
% 0.21/0.42    inference(subsumption_resolution,[],[f329,f29])).
% 0.21/0.42  fof(f329,plain,(
% 0.21/0.42    ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | spl5_2),
% 0.21/0.42    inference(subsumption_resolution,[],[f328,f26])).
% 0.21/0.42  fof(f328,plain,(
% 0.21/0.42    v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | spl5_2),
% 0.21/0.42    inference(subsumption_resolution,[],[f327,f32])).
% 0.21/0.42  fof(f327,plain,(
% 0.21/0.42    ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | spl5_2),
% 0.21/0.42    inference(subsumption_resolution,[],[f326,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f326,plain,(
% 0.21/0.42    r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | spl5_2),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f325])).
% 0.21/0.42  fof(f325,plain,(
% 0.21/0.42    r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | spl5_2),
% 0.21/0.42    inference(resolution,[],[f324,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X0) | r1_waybel_0(X0,X1,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).
% 0.21/0.42  fof(f324,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),u1_struct_0(sK0)) | r1_waybel_0(sK0,sK1,X0)) ) | spl5_2),
% 0.21/0.42    inference(subsumption_resolution,[],[f323,f112])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f111])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    spl5_2 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.42  fof(f323,plain,(
% 0.21/0.42    ( ! [X0] : (r1_waybel_0(sK0,sK1,X0) | v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))),u1_struct_0(sK0))) )),
% 0.21/0.42    inference(resolution,[],[f274,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.42  fof(f274,plain,(
% 0.21/0.42    ( ! [X2] : (m1_subset_1(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X2,k4_yellow_6(sK1,sK2(sK1)))),u1_struct_0(sK0)) | r1_waybel_0(sK0,sK1,X2)) )),
% 0.21/0.42    inference(resolution,[],[f272,f150])).
% 0.21/0.42  fof(f150,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(k2_waybel_0(sK0,sK1,X0),u1_struct_0(sK0))) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f149,f31])).
% 0.21/0.42  fof(f149,plain,(
% 0.21/0.42    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(k2_waybel_0(sK0,sK1,X0),u1_struct_0(sK0))) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f148,f26])).
% 0.21/0.42  fof(f148,plain,(
% 0.21/0.42    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(k2_waybel_0(sK0,sK1,X0),u1_struct_0(sK0))) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f138,f32])).
% 0.21/0.42  fof(f138,plain,(
% 0.21/0.42    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(k2_waybel_0(sK0,sK1,X0),u1_struct_0(sK0))) )),
% 0.21/0.42    inference(resolution,[],[f44,f29])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).
% 0.21/0.42  fof(f272,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,X0)) )),
% 0.21/0.42    inference(resolution,[],[f196,f95])).
% 0.21/0.42  fof(f196,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(sK4(sK0,sK1,X1,X0),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,X1)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f195,f31])).
% 0.21/0.42  fof(f195,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(sK4(sK0,sK1,X1,X0),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,X1)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f194,f26])).
% 0.21/0.42  fof(f194,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(sK4(sK0,sK1,X1,X0),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,X1)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f183,f32])).
% 0.21/0.42  fof(f183,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(sK4(sK0,sK1,X1,X0),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,X1)) )),
% 0.21/0.42    inference(resolution,[],[f37,f29])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1)) | r1_waybel_0(X0,X1,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    ~spl5_2),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f117])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    $false | ~spl5_2),
% 0.21/0.42    inference(subsumption_resolution,[],[f116,f31])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    v2_struct_0(sK0) | ~spl5_2),
% 0.21/0.42    inference(subsumption_resolution,[],[f115,f32])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_2),
% 0.21/0.42    inference(resolution,[],[f113,f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f111])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (14576)------------------------------
% 0.21/0.42  % (14576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (14576)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (14576)Memory used [KB]: 5500
% 0.21/0.42  % (14576)Time elapsed: 0.009 s
% 0.21/0.42  % (14576)------------------------------
% 0.21/0.42  % (14576)------------------------------
% 0.21/0.43  % (14569)Success in time 0.066 s
%------------------------------------------------------------------------------
