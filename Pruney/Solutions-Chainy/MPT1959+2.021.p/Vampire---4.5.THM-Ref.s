%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  143 (1479 expanded)
%              Number of leaves         :   24 ( 369 expanded)
%              Depth                    :   34
%              Number of atoms          :  608 (14954 expanded)
%              Number of equality atoms :   51 ( 203 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (18923)Termination reason: Refutation not found, incomplete strategy

% (18923)Memory used [KB]: 11129
fof(f782,plain,(
    $false ),
    inference(subsumption_resolution,[],[f781,f766])).

fof(f766,plain,(
    ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f698,f103])).

% (18923)Time elapsed: 0.161 s
fof(f103,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(subsumption_resolution,[],[f100,f102])).

fof(f102,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f97,f95])).

fof(f95,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

% (18923)------------------------------
% (18923)------------------------------
fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f100,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f698,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f71,f696])).

fof(f696,plain,(
    u1_struct_0(sK0) = sK1 ),
    inference(subsumption_resolution,[],[f695,f70])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
    & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | v1_subset_1(sK1,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).

fof(f47,plain,
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
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK0),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
        & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
          | v1_subset_1(X1,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
      & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | v1_subset_1(sK1,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f695,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f691])).

fof(f691,plain,
    ( u1_struct_0(sK0) = sK1
    | u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f688,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f688,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | u1_struct_0(sK0) = sK1 ),
    inference(duplicate_literal_removal,[],[f685])).

fof(f685,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | u1_struct_0(sK0) = sK1
    | u1_struct_0(sK0) = sK1 ),
    inference(superposition,[],[f582,f665])).

fof(f665,plain,
    ( sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f373,f70])).

fof(f373,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = X1
      | sK2(u1_struct_0(sK0),X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),X1))) ) ),
    inference(resolution,[],[f369,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f369,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f368,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f368,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f367,f63])).

fof(f63,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f367,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f366,f65])).

fof(f65,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f366,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f365,f67])).

fof(f67,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f365,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

fof(f582,plain,(
    ! [X0] :
      ( r2_hidden(k1_yellow_0(sK0,X0),sK1)
      | u1_struct_0(sK0) = sK1 ) ),
    inference(forward_demodulation,[],[f574,f372])).

fof(f372,plain,(
    ! [X0] : k1_yellow_0(sK0,X0) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))) ),
    inference(resolution,[],[f369,f111])).

fof(f111,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f85,f67])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f574,plain,(
    ! [X0] :
      ( r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))),sK1)
      | u1_struct_0(sK0) = sK1 ) ),
    inference(resolution,[],[f571,f111])).

fof(f571,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1)
      | u1_struct_0(sK0) = sK1 ) ),
    inference(subsumption_resolution,[],[f570,f62])).

fof(f570,plain,(
    ! [X0] :
      ( u1_struct_0(sK0) = sK1
      | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f569,f63])).

fof(f569,plain,(
    ! [X0] :
      ( u1_struct_0(sK0) = sK1
      | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f568,f64])).

fof(f568,plain,(
    ! [X0] :
      ( u1_struct_0(sK0) = sK1
      | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f567,f65])).

fof(f567,plain,(
    ! [X0] :
      ( u1_struct_0(sK0) = sK1
      | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f561,f67])).

fof(f561,plain,(
    ! [X0] :
      ( u1_struct_0(sK0) = sK1
      | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f554,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f554,plain,(
    ! [X1] :
      ( ~ r1_yellow_0(sK0,X1)
      | u1_struct_0(sK0) = sK1
      | r2_hidden(k1_yellow_0(sK0,X1),sK1) ) ),
    inference(resolution,[],[f530,f293])).

fof(f293,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f292,f62])).

fof(f292,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))
      | ~ r1_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f291,f65])).

fof(f291,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))
      | ~ r1_yellow_0(sK0,X0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f290,f66])).

fof(f66,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f290,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))
      | ~ r1_yellow_0(sK0,X0)
      | ~ v1_yellow_0(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f289,f67])).

fof(f289,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))
      | ~ r1_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v1_yellow_0(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f288,f92])).

fof(f92,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f288,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,k1_xboole_0)
      | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f286,f121])).

fof(f121,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f118,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f118,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f117,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f73,f83])).

fof(f83,plain,(
    ! [X0] : v1_xboole_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(X0))
      & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f4,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f286,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))
      | ~ r1_yellow_0(sK0,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X0)
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(superposition,[],[f285,f110])).

fof(f110,plain,(
    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f78,f67])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f285,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X0))
      | ~ r1_yellow_0(sK0,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f96,f67])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f530,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))
      | r2_hidden(k1_yellow_0(sK0,X0),sK1)
      | u1_struct_0(sK0) = sK1 ) ),
    inference(resolution,[],[f520,f129])).

fof(f129,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | u1_struct_0(sK0) = sK1 ),
    inference(subsumption_resolution,[],[f128,f70])).

fof(f128,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(resolution,[],[f81,f72])).

fof(f72,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f520,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK1)
      | ~ r1_orders_2(sK0,X2,k1_yellow_0(sK0,X3))
      | r2_hidden(k1_yellow_0(sK0,X3),sK1) ) ),
    inference(resolution,[],[f513,f111])).

fof(f513,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X0,X1)
      | r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f504,f70])).

fof(f504,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f429,f69])).

fof(f69,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f429,plain,(
    ! [X2,X0,X1] :
      ( ~ v13_waybel_0(X2,sK0)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f101,f67])).

fof(f101,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(subsumption_resolution,[],[f86,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f86,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK5(X0,X1),X1)
                & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1))
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f56,f58,f57])).

fof(f57,plain,(
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
            & r1_orders_2(X0,sK4(X0,X1),X3)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK4(X0,X1),X3)
          & r2_hidden(sK4(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1))
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f71,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f781,plain,(
    r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f780,f696])).

fof(f780,plain,(
    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f704,f68])).

fof(f68,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f704,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f114,f696])).

fof(f114,plain,
    ( r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f113,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f113,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f111,f110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:16:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (18927)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (18928)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (18926)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (18936)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (18943)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (18944)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (18945)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (18937)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (18935)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (18932)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (18921)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (18941)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (18924)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (18929)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (18952)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (18933)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (18922)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (18923)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (18947)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (18939)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (18950)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (18930)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (18940)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (18951)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (18942)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (18931)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (18934)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (18948)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (18946)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (18948)Refutation not found, incomplete strategy% (18948)------------------------------
% 0.21/0.56  % (18948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18948)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18948)Memory used [KB]: 10874
% 0.21/0.56  % (18948)Time elapsed: 0.148 s
% 0.21/0.56  % (18948)------------------------------
% 0.21/0.56  % (18948)------------------------------
% 0.21/0.56  % (18938)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (18927)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.57  % (18930)Refutation not found, incomplete strategy% (18930)------------------------------
% 0.21/0.57  % (18930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (18930)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (18930)Memory used [KB]: 10746
% 0.21/0.57  % (18930)Time elapsed: 0.159 s
% 0.21/0.57  % (18930)------------------------------
% 0.21/0.57  % (18930)------------------------------
% 0.21/0.58  % (18923)Refutation not found, incomplete strategy% (18923)------------------------------
% 0.21/0.58  % (18923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  % (18923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (18923)Memory used [KB]: 11129
% 0.21/0.59  fof(f782,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(subsumption_resolution,[],[f781,f766])).
% 0.21/0.59  fof(f766,plain,(
% 0.21/0.59    ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.21/0.59    inference(subsumption_resolution,[],[f698,f103])).
% 0.21/0.59  % (18923)Time elapsed: 0.161 s
% 0.21/0.59  fof(f103,plain,(
% 0.21/0.59    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f100,f102])).
% 0.21/0.59  fof(f102,plain,(
% 0.21/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.59    inference(forward_demodulation,[],[f97,f95])).
% 0.21/0.59  fof(f95,plain,(
% 0.21/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.59    inference(cnf_transformation,[],[f2])).
% 0.21/0.59  % (18923)------------------------------
% 0.21/0.59  % (18923)------------------------------
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.59  fof(f97,plain,(
% 0.21/0.59    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.59  fof(f100,plain,(
% 0.21/0.59    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.21/0.59    inference(equality_resolution,[],[f80])).
% 0.21/0.59  fof(f80,plain,(
% 0.21/0.59    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f52])).
% 0.21/0.59  fof(f52,plain,(
% 0.21/0.59    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.59    inference(nnf_transformation,[],[f34])).
% 0.21/0.59  fof(f34,plain,(
% 0.21/0.59    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f17])).
% 0.21/0.59  fof(f17,axiom,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.59  fof(f698,plain,(
% 0.21/0.59    v1_subset_1(sK1,sK1) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.21/0.59    inference(backward_demodulation,[],[f71,f696])).
% 0.21/0.59  fof(f696,plain,(
% 0.21/0.59    u1_struct_0(sK0) = sK1),
% 0.21/0.59    inference(subsumption_resolution,[],[f695,f70])).
% 0.21/0.59  fof(f70,plain,(
% 0.21/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f48,plain,(
% 0.21/0.59    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.59    inference(flattening,[],[f45])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.59    inference(nnf_transformation,[],[f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.59    inference(flattening,[],[f23])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.59    inference(pure_predicate_removal,[],[f19])).
% 0.21/0.59  fof(f19,negated_conjecture,(
% 0.21/0.59    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.59    inference(negated_conjecture,[],[f18])).
% 0.21/0.59  fof(f18,conjecture,(
% 0.21/0.59    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.21/0.59  fof(f695,plain,(
% 0.21/0.59    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f691])).
% 0.21/0.59  fof(f691,plain,(
% 0.21/0.59    u1_struct_0(sK0) = sK1 | u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.59    inference(resolution,[],[f688,f76])).
% 0.21/0.59  fof(f76,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f51])).
% 0.21/0.59  fof(f51,plain,(
% 0.21/0.59    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f50])).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),X0)))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.59    inference(flattening,[],[f28])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.21/0.59  fof(f688,plain,(
% 0.21/0.59    r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | u1_struct_0(sK0) = sK1),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f685])).
% 0.21/0.59  fof(f685,plain,(
% 0.21/0.59    r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | u1_struct_0(sK0) = sK1 | u1_struct_0(sK0) = sK1),
% 0.21/0.59    inference(superposition,[],[f582,f665])).
% 0.21/0.59  fof(f665,plain,(
% 0.21/0.59    sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) | u1_struct_0(sK0) = sK1),
% 0.21/0.59    inference(resolution,[],[f373,f70])).
% 0.21/0.59  fof(f373,plain,(
% 0.21/0.59    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X1 | sK2(u1_struct_0(sK0),X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),X1)))) )),
% 0.21/0.59    inference(resolution,[],[f369,f75])).
% 0.21/0.59  fof(f75,plain,(
% 0.21/0.59    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f51])).
% 0.21/0.59  fof(f369,plain,(
% 0.21/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f368,f62])).
% 0.21/0.59  fof(f62,plain,(
% 0.21/0.59    ~v2_struct_0(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f368,plain,(
% 0.21/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f367,f63])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    v3_orders_2(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f367,plain,(
% 0.21/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f366,f65])).
% 0.21/0.59  fof(f65,plain,(
% 0.21/0.59    v5_orders_2(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f366,plain,(
% 0.21/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f365,f67])).
% 0.21/0.59  fof(f67,plain,(
% 0.21/0.59    l1_orders_2(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f365,plain,(
% 0.21/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(resolution,[],[f94,f64])).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    v4_orders_2(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f94,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~v4_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f41])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.59    inference(flattening,[],[f40])).
% 0.21/0.59  fof(f40,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f16])).
% 0.21/0.59  fof(f16,axiom,(
% 0.21/0.59    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).
% 0.21/0.59  fof(f582,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(k1_yellow_0(sK0,X0),sK1) | u1_struct_0(sK0) = sK1) )),
% 0.21/0.59    inference(forward_demodulation,[],[f574,f372])).
% 0.21/0.59  fof(f372,plain,(
% 0.21/0.59    ( ! [X0] : (k1_yellow_0(sK0,X0) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0)))) )),
% 0.21/0.59    inference(resolution,[],[f369,f111])).
% 0.21/0.59  fof(f111,plain,(
% 0.21/0.59    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))) )),
% 0.21/0.59    inference(resolution,[],[f85,f67])).
% 0.21/0.59  fof(f85,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f35])).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f11])).
% 0.21/0.59  fof(f11,axiom,(
% 0.21/0.59    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.21/0.59  fof(f574,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))),sK1) | u1_struct_0(sK0) = sK1) )),
% 0.21/0.59    inference(resolution,[],[f571,f111])).
% 0.21/0.59  fof(f571,plain,(
% 0.21/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1) | u1_struct_0(sK0) = sK1) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f570,f62])).
% 0.21/0.59  fof(f570,plain,(
% 0.21/0.59    ( ! [X0] : (u1_struct_0(sK0) = sK1 | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f569,f63])).
% 0.21/0.59  fof(f569,plain,(
% 0.21/0.59    ( ! [X0] : (u1_struct_0(sK0) = sK1 | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f568,f64])).
% 0.21/0.59  fof(f568,plain,(
% 0.21/0.59    ( ! [X0] : (u1_struct_0(sK0) = sK1 | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f567,f65])).
% 0.21/0.59  fof(f567,plain,(
% 0.21/0.59    ( ! [X0] : (u1_struct_0(sK0) = sK1 | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f561,f67])).
% 0.21/0.59  fof(f561,plain,(
% 0.21/0.59    ( ! [X0] : (u1_struct_0(sK0) = sK1 | r2_hidden(k1_yellow_0(sK0,k5_waybel_0(sK0,X0)),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(resolution,[],[f554,f93])).
% 0.21/0.59  fof(f93,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f41])).
% 0.21/0.59  fof(f554,plain,(
% 0.21/0.59    ( ! [X1] : (~r1_yellow_0(sK0,X1) | u1_struct_0(sK0) = sK1 | r2_hidden(k1_yellow_0(sK0,X1),sK1)) )),
% 0.21/0.59    inference(resolution,[],[f530,f293])).
% 0.21/0.59  fof(f293,plain,(
% 0.21/0.59    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,X0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f292,f62])).
% 0.21/0.59  fof(f292,plain,(
% 0.21/0.59    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,X0) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f291,f65])).
% 0.21/0.59  fof(f291,plain,(
% 0.21/0.59    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,X0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f290,f66])).
% 0.21/0.59  fof(f66,plain,(
% 0.21/0.59    v1_yellow_0(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f290,plain,(
% 0.21/0.59    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,X0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f289,f67])).
% 0.21/0.59  fof(f289,plain,(
% 0.21/0.59    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,X0) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.59    inference(resolution,[],[f288,f92])).
% 0.21/0.59  fof(f92,plain,(
% 0.21/0.59    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f39])).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.59    inference(flattening,[],[f38])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.59    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.59  fof(f14,axiom,(
% 0.21/0.59    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.21/0.59  fof(f288,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_yellow_0(sK0,k1_xboole_0) | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,X0)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f286,f121])).
% 0.21/0.59  fof(f121,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.59    inference(resolution,[],[f118,f98])).
% 0.21/0.59  fof(f98,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f61])).
% 0.21/0.59  fof(f61,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f60])).
% 0.21/0.59  fof(f60,plain,(
% 0.21/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f44,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f20])).
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.59    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.59  fof(f118,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.59    inference(resolution,[],[f117,f84])).
% 0.21/0.59  fof(f84,plain,(
% 0.21/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.59  fof(f117,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK3(X1))) | ~r2_hidden(X2,X0)) )),
% 0.21/0.59    inference(resolution,[],[f73,f83])).
% 0.21/0.59  fof(f83,plain,(
% 0.21/0.59    ( ! [X0] : (v1_xboole_0(sK3(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f54])).
% 0.21/0.59  fof(f54,plain,(
% 0.21/0.59    ! [X0] : (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f4,f53])).
% 0.21/0.59  fof(f53,plain,(
% 0.21/0.59    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.21/0.59  fof(f73,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.59  fof(f286,plain,(
% 0.21/0.59    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0) | ~r1_yellow_0(sK0,X0)) )),
% 0.21/0.59    inference(superposition,[],[f285,f110])).
% 0.21/0.59  fof(f110,plain,(
% 0.21/0.59    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 0.21/0.59    inference(resolution,[],[f78,f67])).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f32])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,axiom,(
% 0.21/0.59    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.21/0.59  fof(f285,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,X1) | ~r1_tarski(X1,X0) | ~r1_yellow_0(sK0,X0)) )),
% 0.21/0.59    inference(resolution,[],[f96,f67])).
% 0.21/0.59  fof(f96,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f43])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.21/0.59    inference(flattening,[],[f42])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f13])).
% 0.21/0.59  fof(f13,axiom,(
% 0.21/0.59    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).
% 0.21/0.59  fof(f530,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) | r2_hidden(k1_yellow_0(sK0,X0),sK1) | u1_struct_0(sK0) = sK1) )),
% 0.21/0.59    inference(resolution,[],[f520,f129])).
% 0.21/0.59  fof(f129,plain,(
% 0.21/0.59    r2_hidden(k3_yellow_0(sK0),sK1) | u1_struct_0(sK0) = sK1),
% 0.21/0.59    inference(subsumption_resolution,[],[f128,f70])).
% 0.21/0.59  fof(f128,plain,(
% 0.21/0.59    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.21/0.59    inference(resolution,[],[f81,f72])).
% 0.21/0.59  fof(f72,plain,(
% 0.21/0.59    ~v1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f81,plain,(
% 0.21/0.59    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f52])).
% 0.21/0.59  fof(f520,plain,(
% 0.21/0.59    ( ! [X2,X3] : (~r2_hidden(X2,sK1) | ~r1_orders_2(sK0,X2,k1_yellow_0(sK0,X3)) | r2_hidden(k1_yellow_0(sK0,X3),sK1)) )),
% 0.21/0.59    inference(resolution,[],[f513,f111])).
% 0.21/0.59  fof(f513,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f504,f70])).
% 0.21/0.59  fof(f504,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK1)) )),
% 0.21/0.59    inference(resolution,[],[f429,f69])).
% 0.21/0.59  fof(f69,plain,(
% 0.21/0.59    v13_waybel_0(sK1,sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f429,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~v13_waybel_0(X2,sK0) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) )),
% 0.21/0.59    inference(resolution,[],[f101,f67])).
% 0.21/0.59  fof(f101,plain,(
% 0.21/0.59    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f86,f74])).
% 0.21/0.59  fof(f74,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f27])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.59    inference(flattening,[],[f26])).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.59    inference(ennf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.59  fof(f86,plain,(
% 0.21/0.59    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f59])).
% 0.21/0.59  fof(f59,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f56,f58,f57])).
% 0.21/0.59  fof(f57,plain,(
% 0.21/0.59    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f58,plain,(
% 0.21/0.59    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f56,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.59    inference(rectify,[],[f55])).
% 0.21/0.59  fof(f55,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.59    inference(nnf_transformation,[],[f37])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.59    inference(flattening,[],[f36])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f15])).
% 0.21/0.59  fof(f15,axiom,(
% 0.21/0.59    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.21/0.59  fof(f71,plain,(
% 0.21/0.59    v1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f781,plain,(
% 0.21/0.59    r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.21/0.59    inference(forward_demodulation,[],[f780,f696])).
% 0.21/0.59  fof(f780,plain,(
% 0.21/0.59    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.21/0.59    inference(subsumption_resolution,[],[f704,f68])).
% 0.21/0.59  fof(f68,plain,(
% 0.21/0.59    ~v1_xboole_0(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f49])).
% 0.21/0.59  fof(f704,plain,(
% 0.21/0.59    v1_xboole_0(sK1) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.21/0.59    inference(backward_demodulation,[],[f114,f696])).
% 0.21/0.59  fof(f114,plain,(
% 0.21/0.59    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.59    inference(resolution,[],[f113,f77])).
% 0.21/0.59  fof(f77,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f31])).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.59    inference(flattening,[],[f30])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.59  fof(f113,plain,(
% 0.21/0.59    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.21/0.59    inference(superposition,[],[f111,f110])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (18927)------------------------------
% 0.21/0.59  % (18927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (18927)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (18927)Memory used [KB]: 7419
% 0.21/0.59  % (18927)Time elapsed: 0.152 s
% 0.21/0.59  % (18927)------------------------------
% 0.21/0.59  % (18927)------------------------------
% 0.21/0.59  % (18918)Success in time 0.223 s
%------------------------------------------------------------------------------
