%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1623+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:11 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 368 expanded)
%              Number of leaves         :   18 ( 138 expanded)
%              Depth                    :   33
%              Number of atoms          :  609 (2719 expanded)
%              Number of equality atoms :   66 ( 439 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f333,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f90,f97,f332])).

fof(f332,plain,
    ( ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f330,f73])).

fof(f73,plain,(
    sP1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f72,f40])).

fof(f40,plain,(
    v1_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v1_waybel_0(sK6,sK4)
    & v1_waybel_0(sK5,sK3)
    & sK5 = sK6
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    & l1_orders_2(sK4)
    & l1_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f8,f22,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v1_waybel_0(X3,X1)
                    & v1_waybel_0(X2,X0)
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_waybel_0(X3,X1)
                  & v1_waybel_0(X2,sK3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
          & l1_orders_2(X1) )
      & l1_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v1_waybel_0(X3,X1)
                & v1_waybel_0(X2,sK3)
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v1_waybel_0(X3,sK4)
              & v1_waybel_0(X2,sK3)
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
      & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
      & l1_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v1_waybel_0(X3,sK4)
            & v1_waybel_0(X2,sK3)
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ? [X3] :
          ( ~ v1_waybel_0(X3,sK4)
          & v1_waybel_0(sK5,sK3)
          & sK5 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ~ v1_waybel_0(X3,sK4)
        & v1_waybel_0(sK5,sK3)
        & sK5 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ~ v1_waybel_0(sK6,sK4)
      & v1_waybel_0(sK5,sK3)
      & sK5 = sK6
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_waybel_0(X3,X1)
                  & v1_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_waybel_0(X3,X1)
                  & v1_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_0)).

fof(f72,plain,
    ( ~ v1_waybel_0(sK5,sK3)
    | sP1(sK5,sK3) ),
    inference(resolution,[],[f69,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v1_waybel_0(X1,X0)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v1_waybel_0(X1,X0)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v1_waybel_0(X1,X0) ) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(X1,X0)
      <=> sP1(X1,X0) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f69,plain,(
    sP2(sK3,sK5) ),
    inference(subsumption_resolution,[],[f67,f34])).

fof(f34,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,
    ( sP2(sK3,sK5)
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f13,f17,f16,f15])).

fof(f15,plain,(
    ! [X3,X0,X2,X1] :
      ( sP0(X3,X0,X2,X1)
    <=> ? [X4] :
          ( r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( sP0(X3,X0,X2,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X3,X4)
                                & r1_orders_2(X0,X2,X4)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_0)).

fof(f330,plain,
    ( ~ sP1(sK5,sK3)
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(resolution,[],[f324,f76])).

fof(f76,plain,(
    ~ sP1(sK5,sK4) ),
    inference(subsumption_resolution,[],[f74,f65])).

fof(f65,plain,(
    ~ v1_waybel_0(sK5,sK4) ),
    inference(forward_demodulation,[],[f41,f39])).

fof(f39,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ~ v1_waybel_0(sK6,sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,
    ( ~ sP1(sK5,sK4)
    | v1_waybel_0(sK5,sK4) ),
    inference(resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    sP2(sK4,sK5) ),
    inference(subsumption_resolution,[],[f68,f35])).

fof(f35,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,
    ( sP2(sK4,sK5)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f58,f66])).

fof(f66,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(forward_demodulation,[],[f38,f39])).

fof(f38,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f23])).

fof(f324,plain,
    ( ! [X0] :
        ( sP1(X0,sK4)
        | ~ sP1(X0,sK3) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f323,f107])).

fof(f107,plain,
    ( ! [X4] :
        ( m1_subset_1(sK8(X4,sK4),u1_struct_0(sK3))
        | sP1(X4,sK4) )
    | ~ spl10_2 ),
    inference(superposition,[],[f49,f99])).

fof(f99,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ spl10_2 ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | u1_struct_0(sK4) = X0 )
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl10_2
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | u1_struct_0(sK4) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),u1_struct_0(X1))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ~ sP0(sK8(X0,X1),X1,sK7(X0,X1),X0)
          & r2_hidden(sK8(X0,X1),X0)
          & r2_hidden(sK7(X0,X1),X0)
          & m1_subset_1(sK8(X0,X1),u1_struct_0(X1))
          & m1_subset_1(sK7(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( sP0(X5,X1,X4,X0)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f26,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ sP0(X3,X1,X2,X0)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ~ sP0(X3,X1,sK7(X0,X1),X0)
            & r2_hidden(X3,X0)
            & r2_hidden(sK7(X0,X1),X0)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ sP0(X3,X1,sK7(X0,X1),X0)
          & r2_hidden(X3,X0)
          & r2_hidden(sK7(X0,X1),X0)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ sP0(sK8(X0,X1),X1,sK7(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK7(X0,X1),X0)
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ sP0(X3,X1,X2,X0)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( sP0(X5,X1,X4,X0)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ~ sP0(X3,X0,X2,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( sP0(X3,X0,X2,X1)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f323,plain,
    ( ! [X0] :
        ( sP1(X0,sK4)
        | ~ m1_subset_1(sK8(X0,sK4),u1_struct_0(sK3))
        | ~ sP1(X0,sK3) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f322,f108])).

fof(f108,plain,
    ( ! [X5] :
        ( m1_subset_1(sK7(X5,sK4),u1_struct_0(sK3))
        | sP1(X5,sK4) )
    | ~ spl10_2 ),
    inference(superposition,[],[f48,f99])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),u1_struct_0(X1))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f322,plain,
    ( ! [X0] :
        ( sP1(X0,sK4)
        | ~ m1_subset_1(sK7(X0,sK4),u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(X0,sK4),u1_struct_0(sK3))
        | ~ sP1(X0,sK3) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f321,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f321,plain,
    ( ! [X0] :
        ( sP1(X0,sK4)
        | ~ r2_hidden(sK8(X0,sK4),X0)
        | ~ m1_subset_1(sK7(X0,sK4),u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(X0,sK4),u1_struct_0(sK3))
        | ~ sP1(X0,sK3) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f319,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f319,plain,
    ( ! [X0] :
        ( sP1(X0,sK4)
        | ~ r2_hidden(sK7(X0,sK4),X0)
        | ~ r2_hidden(sK8(X0,sK4),X0)
        | ~ m1_subset_1(sK7(X0,sK4),u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(X0,sK4),u1_struct_0(sK3))
        | ~ sP1(X0,sK3) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(resolution,[],[f318,f47])).

fof(f47,plain,(
    ! [X4,X0,X5,X1] :
      ( sP0(X5,X1,X4,X0)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f318,plain,
    ( ! [X0] :
        ( ~ sP0(sK7(X0,sK4),sK3,sK8(X0,sK4),X0)
        | sP1(X0,sK4) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,
    ( ! [X0] :
        ( sP1(X0,sK4)
        | ~ sP0(sK7(X0,sK4),sK3,sK8(X0,sK4),X0)
        | ~ sP0(sK7(X0,sK4),sK3,sK8(X0,sK4),X0) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(resolution,[],[f314,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X2,X3),X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_orders_2(X1,X0,X4)
            | ~ r1_orders_2(X1,X2,X4)
            | ~ r2_hidden(X4,X3)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ( r1_orders_2(X1,X0,sK9(X0,X1,X2,X3))
          & r1_orders_2(X1,X2,sK9(X0,X1,X2,X3))
          & r2_hidden(sK9(X0,X1,X2,X3),X3)
          & m1_subset_1(sK9(X0,X1,X2,X3),u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f31,f32])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_orders_2(X1,X0,X5)
          & r1_orders_2(X1,X2,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X0,sK9(X0,X1,X2,X3))
        & r1_orders_2(X1,X2,sK9(X0,X1,X2,X3))
        & r2_hidden(sK9(X0,X1,X2,X3),X3)
        & m1_subset_1(sK9(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r1_orders_2(X1,X0,X4)
            | ~ r1_orders_2(X1,X2,X4)
            | ~ r2_hidden(X4,X3)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ? [X5] :
            ( r1_orders_2(X1,X0,X5)
            & r1_orders_2(X1,X2,X5)
            & r2_hidden(X5,X3)
            & m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP0(X3,X0,X2,X1)
        | ! [X4] :
            ( ~ r1_orders_2(X0,X3,X4)
            | ~ r1_orders_2(X0,X2,X4)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
      & ( ? [X4] :
            ( r1_orders_2(X0,X3,X4)
            & r1_orders_2(X0,X2,X4)
            & r2_hidden(X4,X1)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP0(X3,X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f314,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK9(sK7(X0,sK4),sK3,sK8(X0,sK4),X1),X0)
        | sP1(X0,sK4)
        | ~ sP0(sK7(X0,sK4),sK3,sK8(X0,sK4),X1) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(duplicate_literal_removal,[],[f312])).

fof(f312,plain,
    ( ! [X0,X1] :
        ( sP1(X0,sK4)
        | ~ r2_hidden(sK9(sK7(X0,sK4),sK3,sK8(X0,sK4),X1),X0)
        | ~ sP0(sK7(X0,sK4),sK3,sK8(X0,sK4),X1)
        | ~ sP0(sK7(X0,sK4),sK3,sK8(X0,sK4),X1) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(resolution,[],[f287,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X0,sK9(X0,X1,X2,X3))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f287,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK3,sK7(X1,sK4),sK9(X0,sK3,sK8(X1,sK4),X2))
        | sP1(X1,sK4)
        | ~ r2_hidden(sK9(X0,sK3,sK8(X1,sK4),X2),X1)
        | ~ sP0(X0,sK3,sK8(X1,sK4),X2) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f283,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f283,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK9(X0,sK3,sK8(X1,sK4),X2),u1_struct_0(sK3))
        | ~ r2_hidden(sK9(X0,sK3,sK8(X1,sK4),X2),X1)
        | sP1(X1,sK4)
        | ~ r1_orders_2(sK3,sK7(X1,sK4),sK9(X0,sK3,sK8(X1,sK4),X2))
        | ~ sP0(X0,sK3,sK8(X1,sK4),X2) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(resolution,[],[f282,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X2,sK9(X0,X1,X2,X3))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f282,plain,
    ( ! [X6,X7] :
        ( ~ r1_orders_2(sK3,sK8(X6,sK4),X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK3))
        | ~ r2_hidden(X7,X6)
        | sP1(X6,sK4)
        | ~ r1_orders_2(sK3,sK7(X6,sK4),X7) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f279,f108])).

fof(f279,plain,
    ( ! [X6,X7] :
        ( ~ r1_orders_2(sK3,sK8(X6,sK4),X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK3))
        | ~ r2_hidden(X7,X6)
        | sP1(X6,sK4)
        | ~ m1_subset_1(sK7(X6,sK4),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK7(X6,sK4),X7) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,
    ( ! [X6,X7] :
        ( ~ r1_orders_2(sK3,sK8(X6,sK4),X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK3))
        | ~ r2_hidden(X7,X6)
        | sP1(X6,sK4)
        | ~ m1_subset_1(X7,u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(X6,sK4),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK7(X6,sK4),X7) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(resolution,[],[f271,f256])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK4,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,X1) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f254,f34])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK3,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_orders_2(sK4,X0,X1)
        | ~ l1_orders_2(sK3) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK3,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_orders_2(sK4,X0,X1)
        | ~ l1_orders_2(sK3) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(equality_resolution,[],[f196])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK4,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f195,f129])).

fof(f129,plain,
    ( u1_orders_2(sK3) = u1_orders_2(sK4)
    | ~ spl10_3 ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | u1_orders_2(sK4) = X1 )
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl10_3
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | u1_orders_2(sK4) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f195,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK4))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK4,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f185,f35])).

fof(f185,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK4))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK4,X1,X2)
        | ~ l1_orders_2(sK4)
        | ~ l1_orders_2(X0) )
    | ~ spl10_2 ),
    inference(superposition,[],[f64,f99])).

fof(f64,plain,(
    ! [X4,X0,X5,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_0)).

fof(f271,plain,
    ( ! [X17,X16] :
        ( ~ r1_orders_2(sK4,sK7(X17,sK4),X16)
        | ~ r1_orders_2(sK3,sK8(X17,sK4),X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK3))
        | ~ r2_hidden(X16,X17)
        | sP1(X17,sK4) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK3))
        | ~ m1_subset_1(X16,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK8(X17,sK4),X16)
        | ~ r1_orders_2(sK4,sK7(X17,sK4),X16)
        | ~ r2_hidden(X16,X17)
        | sP1(X17,sK4) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f269,f99])).

fof(f269,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK8(X17,sK4),X16)
        | ~ r1_orders_2(sK4,sK7(X17,sK4),X16)
        | ~ r2_hidden(X16,X17)
        | ~ m1_subset_1(X16,u1_struct_0(sK4))
        | sP1(X17,sK4) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f263,f107])).

fof(f263,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(X17,sK4),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK8(X17,sK4),X16)
        | ~ r1_orders_2(sK4,sK7(X17,sK4),X16)
        | ~ r2_hidden(X16,X17)
        | ~ m1_subset_1(X16,u1_struct_0(sK4))
        | sP1(X17,sK4) )
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(resolution,[],[f256,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK8(X1,X0),X2)
      | ~ r1_orders_2(X0,sK7(X1,X0),X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0) ) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK8(X0,X1),X1,sK7(X0,X1),X0)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ r1_orders_2(X1,X0,X4)
      | ~ r1_orders_2(X1,X2,X4)
      | ~ r2_hidden(X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,
    ( ~ spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f91,f95,f81])).

fof(f81,plain,
    ( spl10_1
  <=> m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f91,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      | u1_orders_2(sK4) = X1
      | ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) ) ),
    inference(superposition,[],[f60,f36])).

fof(f36,plain,(
    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f90,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl10_1 ),
    inference(subsumption_resolution,[],[f88,f35])).

fof(f88,plain,
    ( ~ l1_orders_2(sK4)
    | spl10_1 ),
    inference(resolution,[],[f83,f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f83,plain,
    ( ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f87,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f77,f85,f81])).

fof(f77,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      | u1_struct_0(sK4) = X0
      | ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) ) ),
    inference(superposition,[],[f59,f36])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
