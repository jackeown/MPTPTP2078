%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1644+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:14 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 337 expanded)
%              Number of leaves         :    8 (  88 expanded)
%              Depth                    :    9
%              Number of atoms          :  234 (1147 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f66,f86,f118])).

fof(f118,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f20,f60,f19,f88,f90,f94,f96,f95,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f95,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK2(k4_waybel_0(sK0,sK1),sK1)),sK2(k4_waybel_0(sK0,sK1),sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f20,f19,f55,f87,f90,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,sK7(X0,X1,X3),X3)
      | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,sK7(X0,X1,X3),X3)
      | ~ r2_hidden(X3,X2)
      | k4_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_waybel_0)).

fof(f87,plain,
    ( r2_hidden(sK2(k4_waybel_0(sK0,sK1),sK1),k4_waybel_0(sK0,sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f63,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f63,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl8_2
  <=> r1_tarski(k4_waybel_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f55,plain,(
    m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f20,f19,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_0)).

fof(f96,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2(k4_waybel_0(sK0,sK1),sK1)),u1_struct_0(sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f20,f19,f55,f87,f90,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK7(X0,X1,X3),u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | k4_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2(k4_waybel_0(sK0,sK1),sK1)),sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f20,f19,f55,f87,f90,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k4_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,
    ( m1_subset_1(sK2(k4_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f55,f87,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f88,plain,
    ( ~ r2_hidden(sK2(k4_waybel_0(sK0,sK1),sK1),sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f63,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v13_waybel_0(X1,X0)
          <~> r1_tarski(k4_waybel_0(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v13_waybel_0(X1,X0)
            <=> r1_tarski(k4_waybel_0(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_0)).

fof(f60,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl8_1
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f20,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f20,f19,f68,f71,f67,f75,f55,f69,f41])).

fof(f41,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X4,X3)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X4,X3)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k4_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1),sK4(sK0,sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f20,f19,f59,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_orders_2(X0,sK3(X0,X1),sK4(X0,X1))
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,
    ( ~ v13_waybel_0(sK1,sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f75,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),k4_waybel_0(sK0,sK1))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f64,f70,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),sK1)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f20,f19,f59,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f67,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f20,f19,f59,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,
    ( m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f20,f19,f59,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f20,f19,f59,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK3(X0,X1),X1)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f18,f62,f58])).

fof(f18,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | ~ v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f17,f62,f58])).

fof(f17,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
