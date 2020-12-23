%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1952+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  211 (2145 expanded)
%              Number of leaves         :   22 ( 382 expanded)
%              Depth                    :   19
%              Number of atoms          :  894 (17588 expanded)
%              Number of equality atoms :   45 ( 658 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f80,f85,f90,f95,f100,f105,f109,f267,f325,f334,f345,f354,f361,f395,f405,f410,f418])).

fof(f418,plain,
    ( ~ spl8_2
    | ~ spl8_5
    | ~ spl8_33 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f416,f69])).

fof(f69,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl8_2
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f416,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl8_5
    | ~ spl8_33 ),
    inference(resolution,[],[f394,f84])).

fof(f84,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl8_5
  <=> r2_hidden(k4_tarski(sK4,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f394,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK4,X0),sK1)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl8_33
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(k4_tarski(sK4,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f410,plain,
    ( ~ spl8_1
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl8_1
    | spl8_13 ),
    inference(subsumption_resolution,[],[f168,f406])).

fof(f406,plain,
    ( sK2 = sK5(sK2,sK0,sK1)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f373,f129])).

fof(f129,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f29,f125])).

fof(f125,plain,(
    u1_struct_0(sK0) = u1_struct_0(k13_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f124,f30])).

fof(f30,plain,(
    m4_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
              <~> ! [X3] :
                    ( ! [X4] :
                        ( r1_waybel_0(X0,X4,X2)
                        | ~ r2_hidden(k4_tarski(X4,X3),X1)
                        | ~ l1_waybel_0(X4,X0)
                        | ~ v7_waybel_0(X4)
                        | ~ v4_orders_2(X4)
                        | v2_struct_0(X4) )
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
              <~> ! [X3] :
                    ( ! [X4] :
                        ( r1_waybel_0(X0,X4,X2)
                        | ~ r2_hidden(k4_tarski(X4,X3),X1)
                        | ~ l1_waybel_0(X4,X0)
                        | ~ v7_waybel_0(X4)
                        | ~ v4_orders_2(X4)
                        | v2_struct_0(X4) )
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m4_yellow_6(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1))))
               => ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => ! [X4] :
                            ( ( l1_waybel_0(X4,X0)
                              & v7_waybel_0(X4)
                              & v4_orders_2(X4)
                              & ~ v2_struct_0(X4) )
                           => ( r2_hidden(k4_tarski(X4,X3),X1)
                             => r1_waybel_0(X0,X4,X2) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m4_yellow_6(X1,X0)
              & v8_yellow_6(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1))))
               => ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => ! [X4] :
                            ( ( l1_waybel_0(X4,X0)
                              & v7_waybel_0(X4)
                              & v4_orders_2(X4)
                              & ~ v2_struct_0(X4) )
                           => ( r2_hidden(k4_tarski(X4,X3),X1)
                             => r1_waybel_0(X0,X4,X2) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m4_yellow_6(X1,X0)
            & v8_yellow_6(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1))))
             => ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                     => ! [X4] :
                          ( ( l1_waybel_0(X4,X0)
                            & v7_waybel_0(X4)
                            & v4_orders_2(X4)
                            & ~ v2_struct_0(X4) )
                         => ( r2_hidden(k4_tarski(X4,X3),X1)
                           => r1_waybel_0(X0,X4,X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_yellow_6)).

fof(f124,plain,(
    ! [X0] :
      ( ~ m4_yellow_6(X0,sK0)
      | u1_struct_0(sK0) = u1_struct_0(k13_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f123,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f123,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m4_yellow_6(X0,sK0)
      | u1_struct_0(sK0) = u1_struct_0(k13_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f112,f32])).

fof(f32,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m4_yellow_6(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(k13_yellow_6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f110,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m4_yellow_6(X1,X0)
      | v1_pre_topc(k13_yellow_6(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k13_yellow_6(X0,X1))
        & v1_pre_topc(k13_yellow_6(X0,X1)) )
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k13_yellow_6(X0,X1))
        & v1_pre_topc(k13_yellow_6(X0,X1)) )
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m4_yellow_6(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k13_yellow_6(X0,X1))
        & v1_pre_topc(k13_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k13_yellow_6)).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m4_yellow_6(X1,X0)
      | ~ v1_pre_topc(k13_yellow_6(X0,X1))
      | u1_struct_0(X0) = u1_struct_0(k13_yellow_6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f53,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m4_yellow_6(X1,X0)
      | l1_pre_topc(k13_yellow_6(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m4_yellow_6(X1,X0)
      | ~ v1_pre_topc(k13_yellow_6(X0,X1))
      | ~ l1_pre_topc(k13_yellow_6(X0,X1))
      | u1_struct_0(X0) = u1_struct_0(k13_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m4_yellow_6(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | u1_struct_0(X2) = u1_struct_0(X0)
      | k13_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k13_yellow_6(X0,X1) = X2
              <=> ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                  & u1_struct_0(X2) = u1_struct_0(X0) ) )
              | ~ l1_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m4_yellow_6(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k13_yellow_6(X0,X1) = X2
              <=> ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                  & u1_struct_0(X2) = u1_struct_0(X0) ) )
              | ~ l1_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m4_yellow_6(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m4_yellow_6(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k13_yellow_6(X0,X1) = X2
              <=> ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                  & u1_struct_0(X2) = u1_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d27_yellow_6)).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK0,sK1)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f373,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = sK5(sK2,sK0,sK1)
    | ~ spl8_1 ),
    inference(resolution,[],[f64,f144])).

fof(f144,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,k13_yellow_6(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK5(X0,sK0,sK1) = X0 ) ),
    inference(resolution,[],[f143,f138])).

fof(f138,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_1_yellow_6(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,k13_yellow_6(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f126,f136])).

fof(f136,plain,(
    u1_pre_topc(k13_yellow_6(sK0,sK1)) = a_2_1_yellow_6(sK0,sK1) ),
    inference(resolution,[],[f135,f30])).

fof(f135,plain,(
    ! [X0] :
      ( ~ m4_yellow_6(X0,sK0)
      | a_2_1_yellow_6(sK0,X0) = u1_pre_topc(k13_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f134,f31])).

fof(f134,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m4_yellow_6(X0,sK0)
      | a_2_1_yellow_6(sK0,X0) = u1_pre_topc(k13_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f113,f32])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m4_yellow_6(X1,X0)
      | a_2_1_yellow_6(X0,X1) = u1_pre_topc(k13_yellow_6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f111,f38])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m4_yellow_6(X1,X0)
      | ~ v1_pre_topc(k13_yellow_6(X0,X1))
      | a_2_1_yellow_6(X0,X1) = u1_pre_topc(k13_yellow_6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m4_yellow_6(X1,X0)
      | ~ v1_pre_topc(k13_yellow_6(X0,X1))
      | ~ l1_pre_topc(k13_yellow_6(X0,X1))
      | a_2_1_yellow_6(X0,X1) = u1_pre_topc(k13_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m4_yellow_6(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
      | k13_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f126,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_pre_topc(k13_yellow_6(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,k13_yellow_6(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f122,f125])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK0,sK1))))
      | r2_hidden(X0,u1_pre_topc(k13_yellow_6(sK0,sK1)))
      | ~ v3_pre_topc(X0,k13_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f34,f120])).

fof(f120,plain,(
    l1_pre_topc(k13_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f119,f30])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m4_yellow_6(X0,sK0)
      | l1_pre_topc(k13_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f118,f31])).

fof(f118,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m4_yellow_6(X0,sK0)
      | l1_pre_topc(k13_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f39,f32])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f143,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_yellow_6(sK0,sK1))
      | sK5(X0,sK0,sK1) = X0 ) ),
    inference(resolution,[],[f142,f30])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m4_yellow_6(X0,sK0)
      | sK5(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f141,f31])).

fof(f141,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m4_yellow_6(X0,sK0)
      | sK5(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f50,f32])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | sK5(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r1_waybel_0(X1,X5,X3)
                    | ~ r2_hidden(k4_tarski(X5,X4),X2)
                    | ~ l1_waybel_0(X5,X1)
                    | ~ v7_waybel_0(X5)
                    | ~ v4_orders_2(X5)
                    | v2_struct_0(X5) )
                | ~ r2_hidden(X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r1_waybel_0(X1,X5,X3)
                    | ~ r2_hidden(k4_tarski(X5,X4),X2)
                    | ~ l1_waybel_0(X5,X1)
                    | ~ v7_waybel_0(X5)
                    | ~ v4_orders_2(X5)
                    | v2_struct_0(X5) )
                | ~ r2_hidden(X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m4_yellow_6(X2,X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X3)
                 => ! [X5] :
                      ( ( l1_waybel_0(X5,X1)
                        & v7_waybel_0(X5)
                        & v4_orders_2(X5)
                        & ~ v2_struct_0(X5) )
                     => ( r2_hidden(k4_tarski(X5,X4),X2)
                       => r1_waybel_0(X1,X5,X3) ) ) ) )
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_yellow_6)).

fof(f64,plain,
    ( v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl8_1
  <=> v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f168,plain,
    ( sK2 != sK5(sK2,sK0,sK1)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl8_13
  <=> sK2 = sK5(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f405,plain,
    ( ~ spl8_1
    | spl8_22 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | ~ spl8_1
    | spl8_22 ),
    inference(subsumption_resolution,[],[f403,f64])).

fof(f403,plain,
    ( ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | spl8_22 ),
    inference(subsumption_resolution,[],[f399,f129])).

fof(f399,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | spl8_22 ),
    inference(resolution,[],[f265,f138])).

fof(f265,plain,
    ( ~ r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | spl8_22 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl8_22
  <=> r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f395,plain,
    ( ~ spl8_22
    | spl8_33
    | spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f391,f167,f102,f97,f92,f87,f77,f393,f264])).

fof(f77,plain,
    ( spl8_4
  <=> r1_waybel_0(sK0,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f87,plain,
    ( spl8_6
  <=> l1_waybel_0(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f92,plain,
    ( spl8_7
  <=> v7_waybel_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f97,plain,
    ( spl8_8
  <=> v4_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f102,plain,
    ( spl8_9
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(k4_tarski(sK4,X0),sK1)
        | ~ r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1)) )
    | spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f390,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(backward_demodulation,[],[f114,f125])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | m1_subset_1(X0,u1_struct_0(k13_yellow_6(sK0,sK1))) ) ),
    inference(resolution,[],[f51,f29])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f390,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(k4_tarski(sK4,X0),sK1)
        | ~ r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1)) )
    | spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f389,f30])).

fof(f389,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(k4_tarski(sK4,X0),sK1)
        | ~ m4_yellow_6(sK1,sK0)
        | ~ r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1)) )
    | spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f388,f79])).

fof(f79,plain,
    ( ~ r1_waybel_0(sK0,sK4,sK2)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f388,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK4,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(k4_tarski(sK4,X0),sK1)
        | ~ m4_yellow_6(sK1,sK0)
        | ~ r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1)) )
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_13 ),
    inference(superposition,[],[f387,f169])).

fof(f169,plain,
    ( sK2 = sK5(sK2,sK0,sK1)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f387,plain,
    ( ! [X2,X0,X1] :
        ( r1_waybel_0(sK0,sK4,sK5(X2,sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK5(X2,sK0,X0))
        | ~ r2_hidden(k4_tarski(sK4,X1),X0)
        | ~ m4_yellow_6(X0,sK0)
        | ~ r2_hidden(X2,a_2_1_yellow_6(sK0,X0)) )
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9 ),
    inference(subsumption_resolution,[],[f386,f32])).

fof(f386,plain,
    ( ! [X2,X0,X1] :
        ( ~ m4_yellow_6(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK5(X2,sK0,X0))
        | ~ l1_struct_0(sK0)
        | ~ r2_hidden(k4_tarski(sK4,X1),X0)
        | r1_waybel_0(sK0,sK4,sK5(X2,sK0,X0))
        | ~ r2_hidden(X2,a_2_1_yellow_6(sK0,X0)) )
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9 ),
    inference(subsumption_resolution,[],[f385,f31])).

fof(f385,plain,
    ( ! [X2,X0,X1] :
        ( ~ m4_yellow_6(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK5(X2,sK0,X0))
        | v2_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | ~ r2_hidden(k4_tarski(sK4,X1),X0)
        | r1_waybel_0(sK0,sK4,sK5(X2,sK0,X0))
        | ~ r2_hidden(X2,a_2_1_yellow_6(sK0,X0)) )
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9 ),
    inference(resolution,[],[f370,f89])).

fof(f89,plain,
    ( l1_waybel_0(sK4,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f370,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_waybel_0(sK4,X0)
        | ~ m4_yellow_6(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,sK5(X3,X0,X1))
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ r2_hidden(k4_tarski(sK4,X2),X1)
        | r1_waybel_0(X0,sK4,sK5(X3,X0,X1))
        | ~ r2_hidden(X3,a_2_1_yellow_6(X0,X1)) )
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9 ),
    inference(subsumption_resolution,[],[f369,f99])).

fof(f99,plain,
    ( v4_orders_2(sK4)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f369,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_struct_0(X0)
        | ~ m4_yellow_6(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,sK5(X3,X0,X1))
        | ~ v4_orders_2(sK4)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(sK4,X0)
        | ~ r2_hidden(k4_tarski(sK4,X2),X1)
        | r1_waybel_0(X0,sK4,sK5(X3,X0,X1))
        | ~ r2_hidden(X3,a_2_1_yellow_6(X0,X1)) )
    | ~ spl8_7
    | spl8_9 ),
    inference(subsumption_resolution,[],[f368,f104])).

fof(f104,plain,
    ( ~ v2_struct_0(sK4)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f368,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_struct_0(X0)
        | ~ m4_yellow_6(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r2_hidden(X2,sK5(X3,X0,X1))
        | v2_struct_0(sK4)
        | ~ v4_orders_2(sK4)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(sK4,X0)
        | ~ r2_hidden(k4_tarski(sK4,X2),X1)
        | r1_waybel_0(X0,sK4,sK5(X3,X0,X1))
        | ~ r2_hidden(X3,a_2_1_yellow_6(X0,X1)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f94,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ v7_waybel_0(X5)
      | ~ l1_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,sK5(X0,X1,X2))
      | v2_struct_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X2)
      | r1_waybel_0(X1,X5,sK5(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f94,plain,
    ( v7_waybel_0(sK4)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f361,plain,
    ( spl8_1
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | spl8_1
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f359,f65])).

fof(f65,plain,
    ( ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f359,plain,
    ( v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f357,f129])).

fof(f357,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | ~ spl8_22 ),
    inference(resolution,[],[f266,f137])).

fof(f137,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_yellow_6(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,k13_yellow_6(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f127,f136])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(k13_yellow_6(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,k13_yellow_6(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f121,f125])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK0,sK1))))
      | ~ r2_hidden(X0,u1_pre_topc(k13_yellow_6(sK0,sK1)))
      | v3_pre_topc(X0,k13_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f33,f120])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f266,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f264])).

fof(f354,plain,
    ( spl8_1
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl8_1
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f352,f65])).

fof(f352,plain,
    ( v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f350,f129])).

fof(f350,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | ~ spl8_20 ),
    inference(resolution,[],[f347,f137])).

fof(f347,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f346,f30])).

fof(f346,plain,
    ( ~ m4_yellow_6(sK1,sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ spl8_20 ),
    inference(resolution,[],[f258,f211])).

fof(f211,plain,(
    ! [X0] :
      ( ~ r1_waybel_0(sK0,sK7(sK0,X0,sK2),sK2)
      | ~ m4_yellow_6(X0,sK0)
      | r2_hidden(sK2,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f210,f129])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m4_yellow_6(X0,sK0)
      | ~ r1_waybel_0(sK0,sK7(sK0,X0,X1),X1)
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f209,f31])).

fof(f209,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m4_yellow_6(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_waybel_0(sK0,sK7(sK0,X0,X1),X1)
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f56,f32])).

fof(f56,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_waybel_0(X1,sK7(X1,X2,X3),X3)
      | r2_hidden(X3,a_2_1_yellow_6(X1,X2)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 != X3
      | ~ r1_waybel_0(X1,sK7(X1,X2,X3),X3)
      | r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f258,plain,
    ( r1_waybel_0(sK0,sK7(sK0,sK1,sK2),sK2)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl8_20
  <=> r1_waybel_0(sK0,sK7(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f345,plain,
    ( spl8_1
    | spl8_19 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl8_1
    | spl8_19 ),
    inference(subsumption_resolution,[],[f343,f65])).

fof(f343,plain,
    ( v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | spl8_19 ),
    inference(subsumption_resolution,[],[f341,f129])).

fof(f341,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | spl8_19 ),
    inference(resolution,[],[f338,f137])).

fof(f338,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | spl8_19 ),
    inference(subsumption_resolution,[],[f337,f30])).

fof(f337,plain,
    ( ~ m4_yellow_6(sK1,sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | spl8_19 ),
    inference(subsumption_resolution,[],[f336,f129])).

fof(f336,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m4_yellow_6(sK1,sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | spl8_19 ),
    inference(resolution,[],[f254,f205])).

fof(f205,plain,(
    ! [X0,X1] :
      ( l1_waybel_0(sK7(sK0,X0,X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m4_yellow_6(X0,sK0)
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f204,f31])).

fof(f204,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m4_yellow_6(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_waybel_0(sK7(sK0,X0,X1),sK0)
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f58,f32])).

fof(f58,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | l1_waybel_0(sK7(X1,X2,X3),X1)
      | r2_hidden(X3,a_2_1_yellow_6(X1,X2)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 != X3
      | l1_waybel_0(sK7(X1,X2,X3),X1)
      | r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f254,plain,
    ( ~ l1_waybel_0(sK7(sK0,sK1,sK2),sK0)
    | spl8_19 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl8_19
  <=> l1_waybel_0(sK7(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f334,plain,
    ( spl8_1
    | spl8_18 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | spl8_1
    | spl8_18 ),
    inference(subsumption_resolution,[],[f332,f65])).

fof(f332,plain,
    ( v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | spl8_18 ),
    inference(subsumption_resolution,[],[f330,f129])).

fof(f330,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | spl8_18 ),
    inference(resolution,[],[f327,f137])).

fof(f327,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | spl8_18 ),
    inference(subsumption_resolution,[],[f326,f30])).

fof(f326,plain,
    ( ~ m4_yellow_6(sK1,sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | spl8_18 ),
    inference(resolution,[],[f250,f194])).

fof(f194,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK0,X0,sK2),sK2)
      | ~ m4_yellow_6(X0,sK0)
      | r2_hidden(sK2,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f193,f129])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m4_yellow_6(X0,sK0)
      | r2_hidden(sK6(sK0,X0,X1),X1)
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f192,f31])).

fof(f192,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m4_yellow_6(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK6(sK0,X0,X1),X1)
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f54,f32])).

fof(f54,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK6(X1,X2,X3),X3)
      | r2_hidden(X3,a_2_1_yellow_6(X1,X2)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 != X3
      | r2_hidden(sK6(X1,X2,X3),X3)
      | r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f250,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK2),sK2)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl8_18
  <=> r2_hidden(sK6(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f325,plain,
    ( spl8_1
    | ~ spl8_21 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl8_1
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f323,f65])).

fof(f323,plain,
    ( v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f321,f129])).

fof(f321,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1))
    | ~ spl8_21 ),
    inference(resolution,[],[f318,f137])).

fof(f318,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f317,f31])).

fof(f317,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f316,f129])).

fof(f316,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f315,f30])).

fof(f315,plain,
    ( ~ m4_yellow_6(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f314,f32])).

fof(f314,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m4_yellow_6(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | ~ spl8_21 ),
    inference(resolution,[],[f262,f61])).

fof(f61,plain,(
    ! [X2,X3,X1] :
      ( ~ v2_struct_0(sK7(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | r2_hidden(X3,a_2_1_yellow_6(X1,X2)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 != X3
      | ~ v2_struct_0(sK7(X1,X2,X3))
      | r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f262,plain,
    ( v2_struct_0(sK7(sK0,sK1,sK2))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl8_21
  <=> v2_struct_0(sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f267,plain,
    ( ~ spl8_18
    | ~ spl8_19
    | spl8_20
    | spl8_21
    | spl8_22
    | spl8_1
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f246,f107,f63,f264,f260,f256,f252,f248])).

fof(f107,plain,
    ( spl8_10
  <=> ! [X3,X4] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_waybel_0(sK0,X4,sK2)
        | v2_struct_0(X4)
        | ~ r2_hidden(k4_tarski(X4,X3),sK1)
        | ~ l1_waybel_0(X4,sK0)
        | ~ v7_waybel_0(X4)
        | ~ v4_orders_2(X4)
        | ~ r2_hidden(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f246,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | v2_struct_0(sK7(sK0,sK1,sK2))
    | r1_waybel_0(sK0,sK7(sK0,sK1,sK2),sK2)
    | ~ l1_waybel_0(sK7(sK0,sK1,sK2),sK0)
    | ~ r2_hidden(sK6(sK0,sK1,sK2),sK2)
    | spl8_1
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f245,f190])).

fof(f190,plain,
    ( v4_orders_2(sK7(sK0,sK1,sK2))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f189,f65])).

fof(f189,plain,
    ( v4_orders_2(sK7(sK0,sK1,sK2))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f188,f129])).

fof(f188,plain,
    ( v4_orders_2(sK7(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f179,f30])).

fof(f179,plain,
    ( v4_orders_2(sK7(sK0,sK1,sK2))
    | ~ m4_yellow_6(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f176,f137])).

fof(f176,plain,(
    ! [X0] :
      ( r2_hidden(sK2,a_2_1_yellow_6(sK0,X0))
      | v4_orders_2(sK7(sK0,X0,sK2))
      | ~ m4_yellow_6(X0,sK0) ) ),
    inference(resolution,[],[f175,f129])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m4_yellow_6(X0,sK0)
      | v4_orders_2(sK7(sK0,X0,X1))
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f174,f31])).

fof(f174,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m4_yellow_6(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_orders_2(sK7(sK0,X0,X1))
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f60,f32])).

fof(f60,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v4_orders_2(sK7(X1,X2,X3))
      | r2_hidden(X3,a_2_1_yellow_6(X1,X2)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 != X3
      | v4_orders_2(sK7(X1,X2,X3))
      | r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f245,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | v2_struct_0(sK7(sK0,sK1,sK2))
    | r1_waybel_0(sK0,sK7(sK0,sK1,sK2),sK2)
    | ~ l1_waybel_0(sK7(sK0,sK1,sK2),sK0)
    | ~ v4_orders_2(sK7(sK0,sK1,sK2))
    | ~ r2_hidden(sK6(sK0,sK1,sK2),sK2)
    | spl8_1
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f244,f173])).

fof(f173,plain,
    ( v7_waybel_0(sK7(sK0,sK1,sK2))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f172,f65])).

fof(f172,plain,
    ( v7_waybel_0(sK7(sK0,sK1,sK2))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f171,f129])).

fof(f171,plain,
    ( v7_waybel_0(sK7(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f154,f30])).

fof(f154,plain,
    ( v7_waybel_0(sK7(sK0,sK1,sK2))
    | ~ m4_yellow_6(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f151,f137])).

fof(f151,plain,(
    ! [X0] :
      ( r2_hidden(sK2,a_2_1_yellow_6(sK0,X0))
      | v7_waybel_0(sK7(sK0,X0,sK2))
      | ~ m4_yellow_6(X0,sK0) ) ),
    inference(resolution,[],[f150,f129])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m4_yellow_6(X0,sK0)
      | v7_waybel_0(sK7(sK0,X0,X1))
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f149,f31])).

fof(f149,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m4_yellow_6(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v7_waybel_0(sK7(sK0,X0,X1))
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f59,f32])).

fof(f59,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v7_waybel_0(sK7(X1,X2,X3))
      | r2_hidden(X3,a_2_1_yellow_6(X1,X2)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 != X3
      | v7_waybel_0(sK7(X1,X2,X3))
      | r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f244,plain,
    ( r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | v2_struct_0(sK7(sK0,sK1,sK2))
    | r1_waybel_0(sK0,sK7(sK0,sK1,sK2),sK2)
    | ~ l1_waybel_0(sK7(sK0,sK1,sK2),sK0)
    | ~ v7_waybel_0(sK7(sK0,sK1,sK2))
    | ~ v4_orders_2(sK7(sK0,sK1,sK2))
    | ~ r2_hidden(sK6(sK0,sK1,sK2),sK2)
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f239,f30])).

fof(f239,plain,
    ( ~ m4_yellow_6(sK1,sK0)
    | r2_hidden(sK2,a_2_1_yellow_6(sK0,sK1))
    | v2_struct_0(sK7(sK0,sK1,sK2))
    | r1_waybel_0(sK0,sK7(sK0,sK1,sK2),sK2)
    | ~ l1_waybel_0(sK7(sK0,sK1,sK2),sK0)
    | ~ v7_waybel_0(sK7(sK0,sK1,sK2))
    | ~ v4_orders_2(sK7(sK0,sK1,sK2))
    | ~ r2_hidden(sK6(sK0,sK1,sK2),sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f238,f130])).

fof(f130,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X4,X3),sK1)
        | v2_struct_0(X4)
        | r1_waybel_0(sK0,X4,sK2)
        | ~ l1_waybel_0(X4,sK0)
        | ~ v7_waybel_0(X4)
        | ~ v4_orders_2(X4)
        | ~ r2_hidden(X3,sK2) )
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f108,f128])).

fof(f108,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_waybel_0(sK0,X4,sK2)
        | v2_struct_0(X4)
        | ~ r2_hidden(k4_tarski(X4,X3),sK1)
        | ~ l1_waybel_0(X4,sK0)
        | ~ v7_waybel_0(X4)
        | ~ v4_orders_2(X4)
        | ~ r2_hidden(X3,sK2) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f238,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK7(sK0,X0,sK2),sK6(sK0,X0,sK2)),X0)
      | ~ m4_yellow_6(X0,sK0)
      | r2_hidden(sK2,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f237,f129])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m4_yellow_6(X0,sK0)
      | r2_hidden(k4_tarski(sK7(sK0,X0,X1),sK6(sK0,X0,X1)),X0)
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f236,f31])).

fof(f236,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m4_yellow_6(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(k4_tarski(sK7(sK0,X0,X1),sK6(sK0,X0,X1)),X0)
      | r2_hidden(X1,a_2_1_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f57,f32])).

fof(f57,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(k4_tarski(sK7(X1,X2,X3),sK6(X1,X2,X3)),X2)
      | r2_hidden(X3,a_2_1_yellow_6(X1,X2)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 != X3
      | r2_hidden(k4_tarski(sK7(X1,X2,X3),sK6(X1,X2,X3)),X2)
      | r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,
    ( spl8_1
    | spl8_10 ),
    inference(avatar_split_clause,[],[f20,f107,f63])).

fof(f20,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK2)
      | v2_struct_0(X4)
      | ~ v4_orders_2(X4)
      | ~ v7_waybel_0(X4)
      | ~ l1_waybel_0(X4,sK0)
      | ~ r2_hidden(k4_tarski(X4,X3),sK1)
      | r1_waybel_0(sK0,X4,sK2)
      | v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f105,plain,
    ( ~ spl8_1
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f21,f102,f63])).

fof(f21,plain,
    ( ~ v2_struct_0(sK4)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f100,plain,
    ( ~ spl8_1
    | spl8_8 ),
    inference(avatar_split_clause,[],[f22,f97,f63])).

fof(f22,plain,
    ( v4_orders_2(sK4)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f95,plain,
    ( ~ spl8_1
    | spl8_7 ),
    inference(avatar_split_clause,[],[f23,f92,f63])).

fof(f23,plain,
    ( v7_waybel_0(sK4)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f90,plain,
    ( ~ spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f24,f87,f63])).

fof(f24,plain,
    ( l1_waybel_0(sK4,sK0)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f25,f82,f63])).

fof(f25,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK1)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f80,plain,
    ( ~ spl8_1
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f26,f77,f63])).

fof(f26,plain,
    ( ~ r1_waybel_0(sK0,sK4,sK2)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f28,f67,f63])).

fof(f28,plain,
    ( r2_hidden(sK3,sK2)
    | ~ v3_pre_topc(sK2,k13_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
