%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 (1195 expanded)
%              Number of leaves         :   18 ( 272 expanded)
%              Depth                    :   29
%              Number of atoms          :  507 (10319 expanded)
%              Number of equality atoms :   34 ( 144 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f659,plain,(
    $false ),
    inference(subsumption_resolution,[],[f647,f623])).

fof(f623,plain,(
    v1_subset_1(sK4,sK4) ),
    inference(subsumption_resolution,[],[f549,f175])).

fof(f175,plain,(
    r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f164,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK4)
      | r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f59,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f59,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( r2_hidden(k3_yellow_0(sK3),sK4)
      | ~ v1_subset_1(sK4,u1_struct_0(sK3)) )
    & ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
      | v1_subset_1(sK4,u1_struct_0(sK3)) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v13_waybel_0(sK4,sK3)
    & ~ v1_xboole_0(sK4)
    & l1_orders_2(sK3)
    & v1_yellow_0(sK3)
    & v5_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK3),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK3)) )
          & ( ~ r2_hidden(k3_yellow_0(sK3),X1)
            | v1_subset_1(X1,u1_struct_0(sK3)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v13_waybel_0(X1,sK3)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK3)
      & v1_yellow_0(sK3)
      & v5_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK3),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK3)) )
        & ( ~ r2_hidden(k3_yellow_0(sK3),X1)
          | v1_subset_1(X1,u1_struct_0(sK3)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        & v13_waybel_0(X1,sK3)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK3),sK4)
        | ~ v1_subset_1(sK4,u1_struct_0(sK3)) )
      & ( ~ r2_hidden(k3_yellow_0(sK3),sK4)
        | v1_subset_1(sK4,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & v13_waybel_0(sK4,sK3)
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
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
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f164,plain,
    ( m1_subset_1(k3_yellow_0(sK3),sK4)
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(superposition,[],[f100,f146])).

fof(f146,plain,
    ( u1_struct_0(sK3) = sK4
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f145,f61])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f40])).

fof(f145,plain,
    ( r2_hidden(k3_yellow_0(sK3),sK4)
    | u1_struct_0(sK3) = sK4
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f63,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f63,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) ),
    inference(resolution,[],[f58,f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f58,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f549,plain,
    ( v1_subset_1(sK4,sK4)
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(backward_demodulation,[],[f62,f534])).

fof(f534,plain,(
    u1_struct_0(sK3) = sK4 ),
    inference(subsumption_resolution,[],[f533,f356])).

fof(f356,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(resolution,[],[f244,f91])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f244,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK3))
      | sK4 = X0
      | m1_subset_1(sK7(u1_struct_0(sK3),sK4,X0),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f109,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f109,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | m1_subset_1(sK7(u1_struct_0(sK3),sK4,X1),u1_struct_0(sK3))
      | sK4 = X1 ) ),
    inference(resolution,[],[f61,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK7(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( sP2(X2,sK7(X0,X1,X2),X1)
            & m1_subset_1(sK7(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( sP2(X2,X3,X1)
          & m1_subset_1(X3,X0) )
     => ( sP2(X2,sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( sP2(X2,X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f28,f34])).

fof(f34,plain,(
    ! [X2,X3,X1] :
      ( ( r2_hidden(X3,X1)
      <~> r2_hidden(X3,X2) )
      | ~ sP2(X2,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f533,plain,
    ( u1_struct_0(sK3) = sK4
    | ~ m1_subset_1(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f532,f119])).

fof(f119,plain,(
    sP0(sK4,sK3) ),
    inference(subsumption_resolution,[],[f117,f60])).

fof(f60,plain,(
    v13_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f117,plain,
    ( sP0(sK4,sK3)
    | ~ v13_waybel_0(sK4,sK3) ),
    inference(resolution,[],[f116,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v13_waybel_0(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f116,plain,(
    sP1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f106,f58])).

fof(f106,plain,
    ( sP1(sK3,sK4)
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f61,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f20,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f532,plain,
    ( u1_struct_0(sK3) = sK4
    | ~ m1_subset_1(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ sP0(sK4,sK3) ),
    inference(subsumption_resolution,[],[f525,f175])).

% (32103)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f525,plain,
    ( u1_struct_0(sK3) = sK4
    | ~ m1_subset_1(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4)
    | ~ sP0(sK4,sK3) ),
    inference(resolution,[],[f524,f199])).

fof(f199,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r2_hidden(k3_yellow_0(sK3),X1)
      | ~ sP0(X1,sK3) ) ),
    inference(subsumption_resolution,[],[f198,f100])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(k3_yellow_0(sK3),X1)
      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
      | ~ sP0(X1,sK3) ) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(k3_yellow_0(sK3),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))
      | ~ sP0(X1,sK3) ) ),
    inference(resolution,[],[f103,f67])).

fof(f67,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X0)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X0)
          & r1_orders_2(X1,sK5(X0,X1),sK6(X0,X1))
          & r2_hidden(sK5(X0,X1),X0)
          & m1_subset_1(sK6(X0,X1),u1_struct_0(X1))
          & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X4,X5)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f43,f45,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r1_orders_2(X1,X2,X3)
              & r2_hidden(X2,X0)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r1_orders_2(X1,sK5(X0,X1),X3)
            & r2_hidden(sK5(X0,X1),X0)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r1_orders_2(X1,sK5(X0,X1),X3)
          & r2_hidden(sK5(X0,X1),X0)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(sK6(X0,X1),X0)
        & r1_orders_2(X1,sK5(X0,X1),sK6(X0,X1))
        & r2_hidden(sK5(X0,X1),X0)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r1_orders_2(X1,X2,X3)
                & r2_hidden(X2,X0)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X4,X5)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r1_orders_2(X0,X2,X3)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f103,plain,(
    ! [X0] :
      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f102,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    ! [X0] :
      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f101,f56])).

fof(f56,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    ! [X0] :
      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ v5_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f98,f57])).

fof(f57,plain,(
    v1_yellow_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,(
    ! [X0] :
      ( r1_orders_2(sK3,k3_yellow_0(sK3),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ v1_yellow_0(sK3)
      | ~ v5_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f58,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f524,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(subsumption_resolution,[],[f521,f397])).

fof(f397,plain,
    ( r2_hidden(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(resolution,[],[f356,f342])).

fof(f342,plain,(
    ! [X23] :
      ( ~ m1_subset_1(X23,u1_struct_0(sK3))
      | r2_hidden(X23,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f341,f119])).

fof(f341,plain,(
    ! [X23] :
      ( ~ m1_subset_1(X23,u1_struct_0(sK3))
      | ~ sP0(sK4,sK3)
      | r2_hidden(X23,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f336,f175])).

fof(f336,plain,(
    ! [X23] :
      ( ~ m1_subset_1(X23,u1_struct_0(sK3))
      | ~ r2_hidden(k3_yellow_0(sK3),sK4)
      | ~ sP0(sK4,sK3)
      | r2_hidden(X23,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f199,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | r2_hidden(X0,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f61,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f521,plain,
    ( u1_struct_0(sK3) = sK4
    | ~ r2_hidden(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4) ),
    inference(resolution,[],[f388,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X1,X0)
          | ~ r2_hidden(X1,X2) )
        & ( r2_hidden(X1,X0)
          | r2_hidden(X1,X2) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X2,X3,X1] :
      ( ( ( ~ r2_hidden(X3,X2)
          | ~ r2_hidden(X3,X1) )
        & ( r2_hidden(X3,X2)
          | r2_hidden(X3,X1) ) )
      | ~ sP2(X2,X3,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f388,plain,
    ( sP2(u1_struct_0(sK3),sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)
    | u1_struct_0(sK3) = sK4 ),
    inference(resolution,[],[f287,f91])).

fof(f287,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK3))
      | sK4 = X0
      | sP2(X0,sK7(u1_struct_0(sK3),sK4,X0),sK4) ) ),
    inference(resolution,[],[f111,f87])).

fof(f111,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
      | sP2(X3,sK7(u1_struct_0(sK3),sK4,X3),sK4)
      | sK4 = X3 ) ),
    inference(resolution,[],[f61,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | sP2(X2,sK7(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f62,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(k3_yellow_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f647,plain,(
    ~ v1_subset_1(sK4,sK4) ),
    inference(resolution,[],[f548,f89])).

fof(f89,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f548,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK4)) ),
    inference(backward_demodulation,[],[f61,f534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:04:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (32109)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (32117)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.50  % (32112)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (32108)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (32108)Refutation not found, incomplete strategy% (32108)------------------------------
% 0.21/0.51  % (32108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32108)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32108)Memory used [KB]: 1663
% 0.21/0.51  % (32108)Time elapsed: 0.088 s
% 0.21/0.51  % (32108)------------------------------
% 0.21/0.51  % (32108)------------------------------
% 0.21/0.51  % (32121)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (32119)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (32115)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (32122)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (32105)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (32109)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (32114)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f659,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f647,f623])).
% 0.21/0.52  fof(f623,plain,(
% 0.21/0.52    v1_subset_1(sK4,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f549,f175])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    r2_hidden(k3_yellow_0(sK3),sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f164,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,sK4) | r2_hidden(X0,sK4)) )),
% 0.21/0.52    inference(resolution,[],[f59,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ~v1_xboole_0(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f39,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) & l1_orders_2(sK3) & v1_yellow_0(sK3) & v5_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ? [X1] : ((r2_hidden(k3_yellow_0(sK3),X1) | ~v1_subset_1(X1,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),X1) | v1_subset_1(X1,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(X1,sK3) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK3),sK4) | ~v1_subset_1(sK4,u1_struct_0(sK3))) & (~r2_hidden(k3_yellow_0(sK3),sK4) | v1_subset_1(sK4,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v13_waybel_0(sK4,sK3) & ~v1_xboole_0(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    m1_subset_1(k3_yellow_0(sK3),sK4) | r2_hidden(k3_yellow_0(sK3),sK4)),
% 0.21/0.52    inference(superposition,[],[f100,f146])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    u1_struct_0(sK3) = sK4 | r2_hidden(k3_yellow_0(sK3),sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f145,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    r2_hidden(k3_yellow_0(sK3),sK4) | u1_struct_0(sK3) = sK4 | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(resolution,[],[f63,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ~v1_subset_1(sK4,u1_struct_0(sK3)) | r2_hidden(k3_yellow_0(sK3),sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3))),
% 0.21/0.52    inference(resolution,[],[f58,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    l1_orders_2(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f549,plain,(
% 0.21/0.52    v1_subset_1(sK4,sK4) | ~r2_hidden(k3_yellow_0(sK3),sK4)),
% 0.21/0.52    inference(backward_demodulation,[],[f62,f534])).
% 0.21/0.52  fof(f534,plain,(
% 0.21/0.52    u1_struct_0(sK3) = sK4),
% 0.21/0.52    inference(subsumption_resolution,[],[f533,f356])).
% 0.21/0.52  fof(f356,plain,(
% 0.21/0.52    m1_subset_1(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | u1_struct_0(sK3) = sK4),
% 0.21/0.52    inference(resolution,[],[f244,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | sK4 = X0 | m1_subset_1(sK7(u1_struct_0(sK3),sK4,X0),u1_struct_0(sK3))) )),
% 0.21/0.52    inference(resolution,[],[f109,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | m1_subset_1(sK7(u1_struct_0(sK3),sK4,X1),u1_struct_0(sK3)) | sK4 = X1) )),
% 0.21/0.52    inference(resolution,[],[f61,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK7(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | (sP2(X2,sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (sP2(X2,X3,X1) & m1_subset_1(X3,X0)) => (sP2(X2,sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (sP2(X2,X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(definition_folding,[],[f28,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X2,X3,X1] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) | ~sP2(X2,X3,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.21/0.52  fof(f533,plain,(
% 0.21/0.52    u1_struct_0(sK3) = sK4 | ~m1_subset_1(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3))),
% 0.21/0.52    inference(subsumption_resolution,[],[f532,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    sP0(sK4,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    v13_waybel_0(sK4,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    sP0(sK4,sK3) | ~v13_waybel_0(sK4,sK3)),
% 0.21/0.52    inference(resolution,[],[f116,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP0(X1,X0) | ~v13_waybel_0(X1,X0) | ~sP1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1] : (((v13_waybel_0(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v13_waybel_0(X1,X0))) | ~sP1(X0,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((v13_waybel_0(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    sP1(sK3,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f58])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    sP1(sK3,sK4) | ~l1_orders_2(sK3)),
% 0.21/0.52    inference(resolution,[],[f61,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(definition_folding,[],[f20,f32,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.21/0.52  fof(f532,plain,(
% 0.21/0.52    u1_struct_0(sK3) = sK4 | ~m1_subset_1(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~sP0(sK4,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f525,f175])).
% 0.21/0.52  % (32103)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  fof(f525,plain,(
% 0.21/0.52    u1_struct_0(sK3) = sK4 | ~m1_subset_1(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~r2_hidden(k3_yellow_0(sK3),sK4) | ~sP0(sK4,sK3)),
% 0.21/0.52    inference(resolution,[],[f524,f199])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(k3_yellow_0(sK3),X1) | ~sP0(X1,sK3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f198,f100])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | r2_hidden(X0,X1) | ~r2_hidden(k3_yellow_0(sK3),X1) | ~m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) | ~sP0(X1,sK3)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f197])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | r2_hidden(X0,X1) | ~r2_hidden(k3_yellow_0(sK3),X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(k3_yellow_0(sK3),u1_struct_0(sK3)) | ~sP0(X1,sK3)) )),
% 0.21/0.52    inference(resolution,[],[f103,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK6(X0,X1),X0) & r1_orders_2(X1,sK5(X0,X1),sK6(X0,X1)) & r2_hidden(sK5(X0,X1),X0) & m1_subset_1(sK6(X0,X1),u1_struct_0(X1))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f43,f45,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) => (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK5(X0,X1),X3) & r2_hidden(sK5(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK5(X0,X1),X3) & r2_hidden(sK5(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK6(X0,X1),X0) & r1_orders_2(X1,sK5(X0,X1),sK6(X0,X1)) & r2_hidden(sK5(X0,X1),X0) & m1_subset_1(sK6(X0,X1),u1_struct_0(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X1,X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f31])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK3,k3_yellow_0(sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f102,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ~v2_struct_0(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK3,k3_yellow_0(sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | v2_struct_0(sK3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f101,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    v5_orders_2(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK3,k3_yellow_0(sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v5_orders_2(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f98,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    v1_yellow_0(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X0] : (r1_orders_2(sK3,k3_yellow_0(sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v1_yellow_0(sK3) | ~v5_orders_2(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.52    inference(resolution,[],[f58,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.21/0.52  fof(f524,plain,(
% 0.21/0.52    ~r2_hidden(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4) | u1_struct_0(sK3) = sK4),
% 0.21/0.52    inference(subsumption_resolution,[],[f521,f397])).
% 0.21/0.52  fof(f397,plain,(
% 0.21/0.52    r2_hidden(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | u1_struct_0(sK3) = sK4),
% 0.21/0.52    inference(resolution,[],[f356,f342])).
% 0.21/0.52  fof(f342,plain,(
% 0.21/0.52    ( ! [X23] : (~m1_subset_1(X23,u1_struct_0(sK3)) | r2_hidden(X23,u1_struct_0(sK3))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f341,f119])).
% 0.21/0.52  fof(f341,plain,(
% 0.21/0.52    ( ! [X23] : (~m1_subset_1(X23,u1_struct_0(sK3)) | ~sP0(sK4,sK3) | r2_hidden(X23,u1_struct_0(sK3))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f336,f175])).
% 0.21/0.52  fof(f336,plain,(
% 0.21/0.52    ( ! [X23] : (~m1_subset_1(X23,u1_struct_0(sK3)) | ~r2_hidden(k3_yellow_0(sK3),sK4) | ~sP0(sK4,sK3) | r2_hidden(X23,u1_struct_0(sK3))) )),
% 0.21/0.52    inference(resolution,[],[f199,f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK4) | r2_hidden(X0,u1_struct_0(sK3))) )),
% 0.21/0.52    inference(resolution,[],[f61,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.52  fof(f521,plain,(
% 0.21/0.52    u1_struct_0(sK3) = sK4 | ~r2_hidden(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~r2_hidden(sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4)),
% 0.21/0.52    inference(resolution,[],[f388,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,X2) | ~sP2(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP2(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ! [X2,X3,X1] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | ~sP2(X2,X3,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f34])).
% 0.21/0.52  fof(f388,plain,(
% 0.21/0.52    sP2(u1_struct_0(sK3),sK7(u1_struct_0(sK3),sK4,u1_struct_0(sK3)),sK4) | u1_struct_0(sK3) = sK4),
% 0.21/0.52    inference(resolution,[],[f287,f91])).
% 0.21/0.52  fof(f287,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | sK4 = X0 | sP2(X0,sK7(u1_struct_0(sK3),sK4,X0),sK4)) )),
% 0.21/0.52    inference(resolution,[],[f111,f87])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) | sP2(X3,sK7(u1_struct_0(sK3),sK4,X3),sK4) | sK4 = X3) )),
% 0.21/0.52    inference(resolution,[],[f61,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (X1 = X2 | sP2(X2,sK7(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f51])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    v1_subset_1(sK4,u1_struct_0(sK3)) | ~r2_hidden(k3_yellow_0(sK3),sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f647,plain,(
% 0.21/0.52    ~v1_subset_1(sK4,sK4)),
% 0.21/0.52    inference(resolution,[],[f548,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f47])).
% 0.21/0.52  fof(f548,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(sK4))),
% 0.21/0.52    inference(backward_demodulation,[],[f61,f534])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (32109)------------------------------
% 0.21/0.52  % (32109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32109)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (32109)Memory used [KB]: 1918
% 0.21/0.52  % (32109)Time elapsed: 0.099 s
% 0.21/0.52  % (32109)------------------------------
% 0.21/0.52  % (32109)------------------------------
% 0.21/0.52  % (32100)Success in time 0.156 s
%------------------------------------------------------------------------------
