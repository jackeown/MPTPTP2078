%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 677 expanded)
%              Number of leaves         :   16 ( 198 expanded)
%              Depth                    :   21
%              Number of atoms          :  483 (5095 expanded)
%              Number of equality atoms :   32 ( 199 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(subsumption_resolution,[],[f238,f225])).

fof(f225,plain,(
    m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f221,f49])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

% (32652)Termination reason: Refutation not found, incomplete strategy

fof(f31,plain,
    ( ( r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
    & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | v1_subset_1(sK1,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & v2_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).

% (32652)Memory used [KB]: 10618
% (32652)Time elapsed: 0.104 s
% (32652)------------------------------
% (32652)------------------------------
fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
          & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
            | v1_subset_1(X1,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & v2_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK0),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
        & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
          | v1_subset_1(X1,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & v2_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
      & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | v1_subset_1(sK1,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & v2_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f221,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(superposition,[],[f56,f189])).

fof(f189,plain,(
    u1_struct_0(sK0) = sK1 ),
    inference(subsumption_resolution,[],[f188,f136])).

fof(f136,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f103,f53])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | m1_subset_1(sK5(X1,X2,X1),X1)
      | X1 = X2 ) ),
    inference(forward_demodulation,[],[f102,f78])).

fof(f78,plain,(
    ! [X0] : sK4(X0) = X0 ),
    inference(subsumption_resolution,[],[f77,f65])).

fof(f65,plain,(
    ! [X0] : ~ v1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK4(X0),X0)
      & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f77,plain,(
    ! [X0] :
      ( sK4(X0) = X0
      | v1_subset_1(sK4(X0),X0) ) ),
    inference(resolution,[],[f68,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f102,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK5(X1,X2,X1),X1)
      | sK4(X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(forward_demodulation,[],[f100,f78])).

fof(f100,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK5(X1,X2,sK4(X1)),X1)
      | sK4(X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f70,f64])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK5(X0,X1,X2),X0)
      | X1 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK5(X0,X1,X2),X2)
              | ~ r2_hidden(sK5(X0,X1,X2),X1) )
            & ( r2_hidden(sK5(X0,X1,X2),X2)
              | r2_hidden(sK5(X0,X1,X2),X1) )
            & m1_subset_1(sK5(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X2)
          | ~ r2_hidden(sK5(X0,X1,X2),X1) )
        & ( r2_hidden(sK5(X0,X1,X2),X2)
          | r2_hidden(sK5(X0,X1,X2),X1) )
        & m1_subset_1(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f188,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f187,f104])).

fof(f104,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f76,f55])).

fof(f55,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f68,f53])).

fof(f187,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f175,f98])).

fof(f98,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f97,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f96,f47])).

fof(f47,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f49])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f63,f48])).

fof(f48,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f175,plain,(
    ! [X4] :
      ( ~ r1_orders_2(sK0,X4,sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))
      | ~ r2_hidden(X4,sK1)
      | u1_struct_0(sK0) = sK1 ) ),
    inference(subsumption_resolution,[],[f170,f144])).

fof(f144,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f120,f53])).

fof(f120,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r2_hidden(sK5(X1,X2,X1),X2)
      | X1 = X2 ) ),
    inference(forward_demodulation,[],[f119,f78])).

fof(f119,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK5(X1,X2,X1),X2)
      | sK4(X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f118,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f118,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK5(X1,X2,X1),X2)
      | ~ r2_hidden(sK5(X1,X2,X1),X1)
      | sK4(X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(forward_demodulation,[],[f117,f78])).

fof(f117,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK5(X1,X2,X1),X1)
      | ~ r2_hidden(sK5(X1,X2,sK4(X1)),X2)
      | sK4(X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(forward_demodulation,[],[f115,f78])).

fof(f115,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK5(X1,X2,sK4(X1)),sK4(X1))
      | ~ r2_hidden(sK5(X1,X2,sK4(X1)),X2)
      | sK4(X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f72,f64])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | X1 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f170,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | ~ r1_orders_2(sK0,X4,sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))
      | r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
      | u1_struct_0(sK0) = sK1 ) ),
    inference(resolution,[],[f162,f136])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X0,X1)
      | r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f159,f52])).

fof(f52,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v13_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK0,X0,X1)
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f122,f53])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v13_waybel_0(X2,sK0)
      | ~ r1_orders_2(sK0,X0,X1)
      | r2_hidden(X1,X2) ) ),
    inference(subsumption_resolution,[],[f121,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f57,f49])).

fof(f57,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK2(X0,X1),X3)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
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
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f238,plain,(
    ~ m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f237,f50])).

fof(f50,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f237,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(resolution,[],[f222,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f222,plain,(
    ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f191,f83])).

fof(f83,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(superposition,[],[f65,f78])).

fof(f191,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(superposition,[],[f54,f189])).

fof(f54,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:58:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (32651)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (32652)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (32653)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (32659)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (32664)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (32653)Refutation not found, incomplete strategy% (32653)------------------------------
% 0.22/0.51  % (32653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32653)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (32653)Memory used [KB]: 1663
% 0.22/0.51  % (32653)Time elapsed: 0.091 s
% 0.22/0.51  % (32653)------------------------------
% 0.22/0.51  % (32653)------------------------------
% 0.22/0.51  % (32656)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (32654)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (32660)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (32647)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (32662)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (32667)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (32652)Refutation not found, incomplete strategy% (32652)------------------------------
% 0.22/0.52  % (32652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32648)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (32647)Refutation not found, incomplete strategy% (32647)------------------------------
% 0.22/0.52  % (32647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32668)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (32662)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f238,f225])).
% 0.22/0.52  fof(f225,plain,(
% 0.22/0.52    m1_subset_1(k3_yellow_0(sK0),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f221,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    l1_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  % (32652)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).
% 0.22/0.52  % (32652)Memory used [KB]: 10618
% 0.22/0.52  % (32652)Time elapsed: 0.104 s
% 0.22/0.52  % (32652)------------------------------
% 0.22/0.52  % (32652)------------------------------
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    m1_subset_1(k3_yellow_0(sK0),sK1) | ~l1_orders_2(sK0)),
% 0.22/0.52    inference(superposition,[],[f56,f189])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    u1_struct_0(sK0) = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f188,f136])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1),
% 0.22/0.52    inference(resolution,[],[f103,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | m1_subset_1(sK5(X1,X2,X1),X1) | X1 = X2) )),
% 0.22/0.52    inference(forward_demodulation,[],[f102,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0] : (sK4(X0) = X0) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f77,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_subset_1(sK4(X0),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0] : (~v1_subset_1(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X0] : (sK4(X0) = X0 | v1_subset_1(sK4(X0),X0)) )),
% 0.22/0.52    inference(resolution,[],[f68,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X2,X1] : (m1_subset_1(sK5(X1,X2,X1),X1) | sK4(X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f100,f78])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X2,X1] : (m1_subset_1(sK5(X1,X2,sK4(X1)),X1) | sK4(X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(resolution,[],[f70,f64])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK5(X0,X1,X2),X0) | X1 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1)) & (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1)) & m1_subset_1(sK5(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1)) & (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1)) & m1_subset_1(sK5(X0,X1,X2),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(flattening,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f187,f104])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    r2_hidden(k3_yellow_0(sK0),sK1) | u1_struct_0(sK0) = sK1),
% 0.22/0.52    inference(resolution,[],[f76,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ~v1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    v1_subset_1(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1),
% 0.22/0.52    inference(resolution,[],[f68,f53])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    ~r2_hidden(k3_yellow_0(sK0),sK1) | u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.22/0.52    inference(resolution,[],[f175,f98])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f97,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f96,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    v5_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f95,f49])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(resolution,[],[f63,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    v1_yellow_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_yellow_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    ( ! [X4] : (~r1_orders_2(sK0,X4,sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) | ~r2_hidden(X4,sK1) | u1_struct_0(sK0) = sK1) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f170,f144])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ~r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | u1_struct_0(sK0) = sK1),
% 0.22/0.52    inference(resolution,[],[f120,f53])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~r2_hidden(sK5(X1,X2,X1),X2) | X1 = X2) )),
% 0.22/0.52    inference(forward_demodulation,[],[f119,f78])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~r2_hidden(sK5(X1,X2,X1),X2) | sK4(X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f118,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~r2_hidden(sK5(X1,X2,X1),X2) | ~r2_hidden(sK5(X1,X2,X1),X1) | sK4(X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f117,f78])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~r2_hidden(sK5(X1,X2,X1),X1) | ~r2_hidden(sK5(X1,X2,sK4(X1)),X2) | sK4(X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f115,f78])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~r2_hidden(sK5(X1,X2,sK4(X1)),sK4(X1)) | ~r2_hidden(sK5(X1,X2,sK4(X1)),X2) | sK4(X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(resolution,[],[f72,f64])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | X1 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    ( ! [X4] : (~r2_hidden(X4,sK1) | ~r1_orders_2(sK0,X4,sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) | r2_hidden(sK5(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | u1_struct_0(sK0) = sK1) )),
% 0.22/0.52    inference(resolution,[],[f162,f136])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f159,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    v13_waybel_0(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(sK1,sK0) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1)) )),
% 0.22/0.52    inference(resolution,[],[f122,f53])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,X2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f121,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) )),
% 0.22/0.52    inference(resolution,[],[f57,f49])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(rectify,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.22/0.52  fof(f238,plain,(
% 0.22/0.52    ~m1_subset_1(k3_yellow_0(sK0),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f237,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ~v1_xboole_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    v1_xboole_0(sK1) | ~m1_subset_1(k3_yellow_0(sK0),sK1)),
% 0.22/0.52    inference(resolution,[],[f222,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.52  fof(f222,plain,(
% 0.22/0.52    ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f191,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 0.22/0.52    inference(superposition,[],[f65,f78])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    v1_subset_1(sK1,sK1) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.22/0.52    inference(superposition,[],[f54,f189])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    v1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (32662)------------------------------
% 0.22/0.52  % (32662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32662)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (32662)Memory used [KB]: 1663
% 0.22/0.52  % (32662)Time elapsed: 0.115 s
% 0.22/0.52  % (32662)------------------------------
% 0.22/0.52  % (32662)------------------------------
% 0.22/0.52  % (32665)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (32655)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (32645)Success in time 0.156 s
%------------------------------------------------------------------------------
