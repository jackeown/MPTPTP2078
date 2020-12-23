%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:56 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 731 expanded)
%              Number of leaves         :   19 ( 196 expanded)
%              Depth                    :   30
%              Number of atoms          :  563 (7843 expanded)
%              Number of equality atoms :   48 ( 123 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (28761)Termination reason: Refutation not found, incomplete strategy

% (28761)Memory used [KB]: 10618
% (28761)Time elapsed: 0.038 s
% (28761)------------------------------
% (28761)------------------------------
fof(f241,plain,(
    $false ),
    inference(global_subsumption,[],[f238,f240])).

fof(f240,plain,(
    ~ m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f239,f55])).

fof(f55,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f239,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(resolution,[],[f231,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f231,plain,(
    ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f216,f90])).

fof(f90,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(superposition,[],[f76,f88])).

fof(f88,plain,(
    ! [X0] : sK4(X0) = X0 ),
    inference(subsumption_resolution,[],[f87,f76])).

fof(f87,plain,(
    ! [X0] :
      ( sK4(X0) = X0
      | v1_subset_1(sK4(X0),X0) ) ),
    inference(resolution,[],[f81,f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK4(X0),X0)
      & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f76,plain,(
    ! [X0] : ~ v1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

fof(f216,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(superposition,[],[f59,f210])).

fof(f210,plain,(
    u1_struct_0(sK0) = sK1 ),
    inference(subsumption_resolution,[],[f209,f58])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f209,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,
    ( u1_struct_0(sK0) = sK1
    | u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f205,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f205,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1)
    | u1_struct_0(sK0) = sK1 ),
    inference(subsumption_resolution,[],[f204,f58])).

fof(f204,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1)
    | u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1)
    | u1_struct_0(sK0) = sK1
    | u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f201,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f201,plain,
    ( ~ m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1)
    | u1_struct_0(sK0) = sK1 ),
    inference(subsumption_resolution,[],[f200,f136])).

fof(f136,plain,(
    ! [X0] :
      ( r1_yellow_0(sK0,k5_waybel_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f135,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f135,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_yellow_0(sK0,k5_waybel_0(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f134,f50])).

fof(f50,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_yellow_0(sK0,k5_waybel_0(sK0,X0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f133,f52])).

fof(f52,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f133,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | r1_yellow_0(sK0,k5_waybel_0(sK0,X0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f132,f54])).

fof(f54,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | r1_yellow_0(sK0,k5_waybel_0(sK0,X0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f71,f51])).

fof(f51,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_waybel_0)).

fof(f200,plain,
    ( ~ m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1)
    | u1_struct_0(sK0) = sK1
    | ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK5(u1_struct_0(sK0),sK1))) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,
    ( ~ m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1)
    | u1_struct_0(sK0) = sK1
    | ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK5(u1_struct_0(sK0),sK1)))
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f195,f182])).

fof(f182,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK5(u1_struct_0(sK0),sK1))
    | ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK5(u1_struct_0(sK0),sK1)))
    | u1_struct_0(sK0) = sK1 ),
    inference(superposition,[],[f130,f177])).

fof(f177,plain,
    ( sK5(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK5(u1_struct_0(sK0),sK1)))
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f148,f58])).

fof(f148,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = X3
      | sK5(u1_struct_0(sK0),X3) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK5(u1_struct_0(sK0),X3))) ) ),
    inference(resolution,[],[f142,f78])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f141,f49])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f140,f50])).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f52])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f54])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f72,f51])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f130,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))
      | ~ r1_yellow_0(sK0,X0) ) ),
    inference(forward_demodulation,[],[f129,f85])).

fof(f85,plain,(
    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f63,f54])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f129,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f128,f49])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f52])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f126,f53])).

fof(f53,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))
      | ~ v1_yellow_0(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f125,f54])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))
      | ~ l1_orders_2(sK0)
      | ~ v1_yellow_0(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f124,f61])).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f124,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | ~ r1_tarski(k1_xboole_0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))
      | ~ l1_orders_2(sK0)
      | ~ v1_yellow_0(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f123,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK0,X1)
      | ~ r1_yellow_0(sK0,X0)
      | ~ r1_tarski(X1,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X0)) ) ),
    inference(resolution,[],[f70,f54])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f195,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,sK1)
      | u1_struct_0(sK0) = sK1 ) ),
    inference(subsumption_resolution,[],[f194,f58])).

fof(f194,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,sK1)
      | u1_struct_0(sK0) = sK1 ) ),
    inference(subsumption_resolution,[],[f191,f57])).

fof(f57,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f191,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v13_waybel_0(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,sK1)
      | u1_struct_0(sK0) = sK1 ) ),
    inference(resolution,[],[f189,f92])).

fof(f92,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f86,f60])).

fof(f60,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f81,f58])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v13_waybel_0(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f188,f54])).

fof(f188,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(subsumption_resolution,[],[f64,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f64,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).

fof(f41,plain,(
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

fof(f42,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f20])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f59,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f238,plain,(
    m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f230,f54])).

fof(f230,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(superposition,[],[f62,f210])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:15:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.37  ipcrm: permission denied for id (789315584)
% 0.22/0.38  ipcrm: permission denied for id (791478274)
% 0.22/0.38  ipcrm: permission denied for id (791511043)
% 0.22/0.38  ipcrm: permission denied for id (791543812)
% 0.22/0.38  ipcrm: permission denied for id (791576581)
% 0.22/0.38  ipcrm: permission denied for id (789348358)
% 0.22/0.38  ipcrm: permission denied for id (789381127)
% 0.22/0.38  ipcrm: permission denied for id (791609352)
% 0.22/0.38  ipcrm: permission denied for id (791642121)
% 0.22/0.39  ipcrm: permission denied for id (794755082)
% 0.22/0.39  ipcrm: permission denied for id (791707659)
% 0.22/0.39  ipcrm: permission denied for id (789446668)
% 0.22/0.39  ipcrm: permission denied for id (794787853)
% 0.22/0.39  ipcrm: permission denied for id (791773198)
% 0.22/0.39  ipcrm: permission denied for id (794820623)
% 0.22/0.39  ipcrm: permission denied for id (791838736)
% 0.22/0.39  ipcrm: permission denied for id (794853393)
% 0.22/0.40  ipcrm: permission denied for id (789577746)
% 0.22/0.40  ipcrm: permission denied for id (789610515)
% 0.22/0.40  ipcrm: permission denied for id (791904276)
% 0.22/0.40  ipcrm: permission denied for id (791937045)
% 0.22/0.40  ipcrm: permission denied for id (794886166)
% 0.22/0.40  ipcrm: permission denied for id (792002583)
% 0.22/0.40  ipcrm: permission denied for id (796229656)
% 0.22/0.40  ipcrm: permission denied for id (792068121)
% 0.22/0.40  ipcrm: permission denied for id (792100890)
% 0.22/0.41  ipcrm: permission denied for id (794951707)
% 0.22/0.41  ipcrm: permission denied for id (796262428)
% 0.22/0.41  ipcrm: permission denied for id (792199197)
% 0.22/0.41  ipcrm: permission denied for id (796295198)
% 0.22/0.41  ipcrm: permission denied for id (792264735)
% 0.22/0.41  ipcrm: permission denied for id (792297504)
% 0.22/0.41  ipcrm: permission denied for id (789807137)
% 0.22/0.41  ipcrm: permission denied for id (789839906)
% 0.22/0.42  ipcrm: permission denied for id (789872675)
% 0.22/0.42  ipcrm: permission denied for id (795050020)
% 0.22/0.42  ipcrm: permission denied for id (792363045)
% 0.22/0.42  ipcrm: permission denied for id (792395814)
% 0.22/0.42  ipcrm: permission denied for id (792428583)
% 0.22/0.42  ipcrm: permission denied for id (795082792)
% 0.22/0.42  ipcrm: permission denied for id (796327977)
% 0.22/0.42  ipcrm: permission denied for id (796360746)
% 0.22/0.43  ipcrm: permission denied for id (792559659)
% 0.22/0.43  ipcrm: permission denied for id (796393516)
% 0.22/0.43  ipcrm: permission denied for id (792625197)
% 0.22/0.43  ipcrm: permission denied for id (795213870)
% 0.22/0.43  ipcrm: permission denied for id (795246639)
% 0.22/0.43  ipcrm: permission denied for id (792756272)
% 0.22/0.43  ipcrm: permission denied for id (792789041)
% 0.22/0.43  ipcrm: permission denied for id (792821810)
% 0.22/0.43  ipcrm: permission denied for id (792854579)
% 0.22/0.44  ipcrm: permission denied for id (795279412)
% 0.22/0.44  ipcrm: permission denied for id (795312181)
% 0.22/0.44  ipcrm: permission denied for id (797016118)
% 0.22/0.44  ipcrm: permission denied for id (790036535)
% 0.22/0.44  ipcrm: permission denied for id (792985656)
% 0.22/0.44  ipcrm: permission denied for id (790102073)
% 0.22/0.44  ipcrm: permission denied for id (793018426)
% 0.22/0.44  ipcrm: permission denied for id (790134843)
% 0.22/0.45  ipcrm: permission denied for id (795377724)
% 0.22/0.45  ipcrm: permission denied for id (793083965)
% 0.22/0.45  ipcrm: permission denied for id (793116734)
% 0.22/0.45  ipcrm: permission denied for id (793149503)
% 0.22/0.45  ipcrm: permission denied for id (795410496)
% 0.22/0.45  ipcrm: permission denied for id (793215041)
% 0.22/0.45  ipcrm: permission denied for id (793247810)
% 0.22/0.45  ipcrm: permission denied for id (796459075)
% 0.22/0.46  ipcrm: permission denied for id (795476036)
% 0.22/0.46  ipcrm: permission denied for id (793346117)
% 0.22/0.46  ipcrm: permission denied for id (793378886)
% 0.22/0.46  ipcrm: permission denied for id (795508807)
% 0.22/0.46  ipcrm: permission denied for id (793444424)
% 0.22/0.46  ipcrm: permission denied for id (793477193)
% 0.22/0.46  ipcrm: permission denied for id (790298698)
% 0.22/0.46  ipcrm: permission denied for id (796491851)
% 0.22/0.47  ipcrm: permission denied for id (795574348)
% 0.22/0.47  ipcrm: permission denied for id (790364237)
% 0.22/0.47  ipcrm: permission denied for id (795607118)
% 0.22/0.47  ipcrm: permission denied for id (793641039)
% 0.22/0.47  ipcrm: permission denied for id (795639888)
% 0.22/0.47  ipcrm: permission denied for id (793706577)
% 0.22/0.47  ipcrm: permission denied for id (790495314)
% 0.22/0.47  ipcrm: permission denied for id (790528083)
% 0.22/0.47  ipcrm: permission denied for id (790560852)
% 0.22/0.48  ipcrm: permission denied for id (790626389)
% 0.22/0.48  ipcrm: permission denied for id (793739350)
% 0.22/0.48  ipcrm: permission denied for id (795672663)
% 0.22/0.48  ipcrm: permission denied for id (793804888)
% 0.22/0.48  ipcrm: permission denied for id (790691929)
% 0.22/0.48  ipcrm: permission denied for id (795705434)
% 0.22/0.48  ipcrm: permission denied for id (790757467)
% 0.22/0.48  ipcrm: permission denied for id (793870428)
% 0.22/0.49  ipcrm: permission denied for id (796524637)
% 0.22/0.49  ipcrm: permission denied for id (790888542)
% 0.22/0.49  ipcrm: permission denied for id (790921311)
% 0.22/0.49  ipcrm: permission denied for id (793935968)
% 0.22/0.49  ipcrm: permission denied for id (796557409)
% 0.22/0.49  ipcrm: permission denied for id (797048930)
% 0.22/0.49  ipcrm: permission denied for id (790986851)
% 0.22/0.49  ipcrm: permission denied for id (791019620)
% 0.22/0.49  ipcrm: permission denied for id (791052389)
% 0.22/0.50  ipcrm: permission denied for id (796622950)
% 0.22/0.50  ipcrm: permission denied for id (791085159)
% 0.22/0.50  ipcrm: permission denied for id (794067048)
% 0.22/0.50  ipcrm: permission denied for id (796655721)
% 0.22/0.50  ipcrm: permission denied for id (795902058)
% 0.22/0.50  ipcrm: permission denied for id (791150699)
% 0.22/0.50  ipcrm: permission denied for id (794165356)
% 0.22/0.50  ipcrm: permission denied for id (791183469)
% 0.22/0.51  ipcrm: permission denied for id (794198126)
% 0.22/0.51  ipcrm: permission denied for id (795934831)
% 0.22/0.51  ipcrm: permission denied for id (796885104)
% 0.22/0.51  ipcrm: permission denied for id (791281777)
% 0.22/0.51  ipcrm: permission denied for id (794296434)
% 0.22/0.51  ipcrm: permission denied for id (796000371)
% 0.22/0.51  ipcrm: permission denied for id (796033140)
% 0.22/0.51  ipcrm: permission denied for id (794394741)
% 0.22/0.52  ipcrm: permission denied for id (796065910)
% 0.22/0.52  ipcrm: permission denied for id (791347319)
% 0.22/0.52  ipcrm: permission denied for id (794460280)
% 0.22/0.52  ipcrm: permission denied for id (794493049)
% 0.22/0.52  ipcrm: permission denied for id (794558587)
% 0.22/0.52  ipcrm: permission denied for id (796131452)
% 0.22/0.52  ipcrm: permission denied for id (794624125)
% 0.22/0.52  ipcrm: permission denied for id (794656894)
% 0.22/0.53  ipcrm: permission denied for id (796950655)
% 0.72/0.64  % (28769)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.72/0.65  % (28777)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.72/0.66  % (28761)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.28/0.67  % (28761)Refutation not found, incomplete strategy% (28761)------------------------------
% 1.28/0.67  % (28761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.67  % (28777)Refutation found. Thanks to Tanya!
% 1.28/0.67  % SZS status Theorem for theBenchmark
% 1.28/0.67  % SZS output start Proof for theBenchmark
% 1.28/0.67  % (28761)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.67  
% 1.28/0.67  % (28761)Memory used [KB]: 10618
% 1.28/0.67  % (28761)Time elapsed: 0.038 s
% 1.28/0.67  % (28761)------------------------------
% 1.28/0.67  % (28761)------------------------------
% 1.28/0.67  fof(f241,plain,(
% 1.28/0.67    $false),
% 1.28/0.67    inference(global_subsumption,[],[f238,f240])).
% 1.28/0.67  fof(f240,plain,(
% 1.28/0.67    ~m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.28/0.67    inference(subsumption_resolution,[],[f239,f55])).
% 1.28/0.67  fof(f55,plain,(
% 1.28/0.67    ~v1_xboole_0(sK1)),
% 1.28/0.67    inference(cnf_transformation,[],[f38])).
% 1.28/0.67  fof(f38,plain,(
% 1.28/0.67    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.28/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 1.28/0.67  fof(f36,plain,(
% 1.28/0.67    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f37,plain,(
% 1.28/0.67    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f35,plain,(
% 1.28/0.67    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.28/0.67    inference(flattening,[],[f34])).
% 1.28/0.67  fof(f34,plain,(
% 1.28/0.67    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.28/0.67    inference(nnf_transformation,[],[f16])).
% 1.28/0.67  fof(f16,plain,(
% 1.28/0.67    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.28/0.67    inference(flattening,[],[f15])).
% 1.28/0.67  fof(f15,plain,(
% 1.28/0.67    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.28/0.67    inference(ennf_transformation,[],[f14])).
% 1.28/0.67  fof(f14,negated_conjecture,(
% 1.28/0.67    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.28/0.67    inference(negated_conjecture,[],[f13])).
% 1.28/0.67  fof(f13,conjecture,(
% 1.28/0.67    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.28/0.67  fof(f239,plain,(
% 1.28/0.67    v1_xboole_0(sK1) | ~m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.28/0.67    inference(resolution,[],[f231,f77])).
% 1.28/0.67  fof(f77,plain,(
% 1.28/0.67    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f28])).
% 1.28/0.67  fof(f28,plain,(
% 1.28/0.67    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.28/0.67    inference(flattening,[],[f27])).
% 1.28/0.67  fof(f27,plain,(
% 1.28/0.67    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.28/0.67    inference(ennf_transformation,[],[f4])).
% 1.28/0.67  fof(f4,axiom,(
% 1.28/0.67    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.28/0.67  fof(f231,plain,(
% 1.28/0.67    ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.28/0.67    inference(subsumption_resolution,[],[f216,f90])).
% 1.28/0.67  fof(f90,plain,(
% 1.28/0.67    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 1.28/0.67    inference(superposition,[],[f76,f88])).
% 1.28/0.67  fof(f88,plain,(
% 1.28/0.67    ( ! [X0] : (sK4(X0) = X0) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f87,f76])).
% 1.28/0.67  fof(f87,plain,(
% 1.28/0.67    ( ! [X0] : (sK4(X0) = X0 | v1_subset_1(sK4(X0),X0)) )),
% 1.28/0.67    inference(resolution,[],[f81,f75])).
% 1.28/0.67  fof(f75,plain,(
% 1.28/0.67    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(X0))) )),
% 1.28/0.67    inference(cnf_transformation,[],[f45])).
% 1.28/0.67  fof(f45,plain,(
% 1.28/0.67    ! [X0] : (~v1_subset_1(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)))),
% 1.28/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f44])).
% 1.28/0.67  fof(f44,plain,(
% 1.28/0.67    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0))))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f3,axiom,(
% 1.28/0.67    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 1.28/0.67  fof(f81,plain,(
% 1.28/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f48])).
% 1.28/0.67  fof(f48,plain,(
% 1.28/0.67    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.67    inference(nnf_transformation,[],[f31])).
% 1.28/0.67  fof(f31,plain,(
% 1.28/0.67    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.67    inference(ennf_transformation,[],[f12])).
% 1.28/0.67  fof(f12,axiom,(
% 1.28/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.28/0.67  fof(f76,plain,(
% 1.28/0.67    ( ! [X0] : (~v1_subset_1(sK4(X0),X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f45])).
% 1.28/0.67  fof(f216,plain,(
% 1.28/0.67    v1_subset_1(sK1,sK1) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.28/0.67    inference(superposition,[],[f59,f210])).
% 1.28/0.67  fof(f210,plain,(
% 1.28/0.67    u1_struct_0(sK0) = sK1),
% 1.28/0.67    inference(subsumption_resolution,[],[f209,f58])).
% 1.28/0.67  fof(f58,plain,(
% 1.28/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.67    inference(cnf_transformation,[],[f38])).
% 1.28/0.67  fof(f209,plain,(
% 1.28/0.67    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.67    inference(duplicate_literal_removal,[],[f206])).
% 1.28/0.67  fof(f206,plain,(
% 1.28/0.67    u1_struct_0(sK0) = sK1 | u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.67    inference(resolution,[],[f205,f79])).
% 1.28/0.67  fof(f79,plain,(
% 1.28/0.67    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.28/0.67    inference(cnf_transformation,[],[f47])).
% 1.28/0.67  fof(f47,plain,(
% 1.28/0.67    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f46])).
% 1.28/0.67  fof(f46,plain,(
% 1.28/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),X0)))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f30,plain,(
% 1.28/0.67    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.67    inference(flattening,[],[f29])).
% 1.28/0.67  fof(f29,plain,(
% 1.28/0.67    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.67    inference(ennf_transformation,[],[f2])).
% 1.28/0.67  fof(f2,axiom,(
% 1.28/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 1.28/0.67  fof(f205,plain,(
% 1.28/0.67    r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1) | u1_struct_0(sK0) = sK1),
% 1.28/0.67    inference(subsumption_resolution,[],[f204,f58])).
% 1.28/0.67  fof(f204,plain,(
% 1.28/0.67    r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1) | u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.67    inference(duplicate_literal_removal,[],[f203])).
% 1.28/0.67  fof(f203,plain,(
% 1.28/0.67    r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1) | u1_struct_0(sK0) = sK1 | u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.67    inference(resolution,[],[f201,f78])).
% 1.28/0.67  fof(f78,plain,(
% 1.28/0.67    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.28/0.67    inference(cnf_transformation,[],[f47])).
% 1.28/0.67  fof(f201,plain,(
% 1.28/0.67    ~m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1) | u1_struct_0(sK0) = sK1),
% 1.28/0.67    inference(subsumption_resolution,[],[f200,f136])).
% 1.28/0.67  fof(f136,plain,(
% 1.28/0.67    ( ! [X0] : (r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f135,f49])).
% 1.28/0.67  fof(f49,plain,(
% 1.28/0.67    ~v2_struct_0(sK0)),
% 1.28/0.67    inference(cnf_transformation,[],[f38])).
% 1.28/0.67  fof(f135,plain,(
% 1.28/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f134,f50])).
% 1.28/0.67  fof(f50,plain,(
% 1.28/0.67    v3_orders_2(sK0)),
% 1.28/0.67    inference(cnf_transformation,[],[f38])).
% 1.28/0.67  fof(f134,plain,(
% 1.28/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f133,f52])).
% 1.28/0.67  fof(f52,plain,(
% 1.28/0.67    v5_orders_2(sK0)),
% 1.28/0.67    inference(cnf_transformation,[],[f38])).
% 1.28/0.67  fof(f133,plain,(
% 1.28/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f132,f54])).
% 1.28/0.67  fof(f54,plain,(
% 1.28/0.67    l1_orders_2(sK0)),
% 1.28/0.67    inference(cnf_transformation,[],[f38])).
% 1.28/0.67  fof(f132,plain,(
% 1.28/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(resolution,[],[f71,f51])).
% 1.28/0.67  fof(f51,plain,(
% 1.28/0.67    v4_orders_2(sK0)),
% 1.28/0.67    inference(cnf_transformation,[],[f38])).
% 1.28/0.67  fof(f71,plain,(
% 1.28/0.67    ( ! [X0,X1] : (~v4_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f24])).
% 1.28/0.67  fof(f24,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.28/0.67    inference(flattening,[],[f23])).
% 1.28/0.67  fof(f23,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.28/0.67    inference(ennf_transformation,[],[f11])).
% 1.28/0.67  fof(f11,axiom,(
% 1.28/0.67    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_waybel_0)).
% 1.28/0.67  fof(f200,plain,(
% 1.28/0.67    ~m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1) | u1_struct_0(sK0) = sK1 | ~r1_yellow_0(sK0,k5_waybel_0(sK0,sK5(u1_struct_0(sK0),sK1)))),
% 1.28/0.67    inference(duplicate_literal_removal,[],[f199])).
% 1.28/0.67  fof(f199,plain,(
% 1.28/0.67    ~m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1) | u1_struct_0(sK0) = sK1 | ~r1_yellow_0(sK0,k5_waybel_0(sK0,sK5(u1_struct_0(sK0),sK1))) | u1_struct_0(sK0) = sK1),
% 1.28/0.67    inference(resolution,[],[f195,f182])).
% 1.28/0.67  fof(f182,plain,(
% 1.28/0.67    r1_orders_2(sK0,k3_yellow_0(sK0),sK5(u1_struct_0(sK0),sK1)) | ~r1_yellow_0(sK0,k5_waybel_0(sK0,sK5(u1_struct_0(sK0),sK1))) | u1_struct_0(sK0) = sK1),
% 1.28/0.67    inference(superposition,[],[f130,f177])).
% 1.28/0.67  fof(f177,plain,(
% 1.28/0.67    sK5(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK5(u1_struct_0(sK0),sK1))) | u1_struct_0(sK0) = sK1),
% 1.28/0.67    inference(resolution,[],[f148,f58])).
% 1.28/0.67  fof(f148,plain,(
% 1.28/0.67    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X3 | sK5(u1_struct_0(sK0),X3) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK5(u1_struct_0(sK0),X3)))) )),
% 1.28/0.67    inference(resolution,[],[f142,f78])).
% 1.28/0.67  fof(f142,plain,(
% 1.28/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f141,f49])).
% 1.28/0.67  fof(f141,plain,(
% 1.28/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f140,f50])).
% 1.28/0.67  fof(f140,plain,(
% 1.28/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f139,f52])).
% 1.28/0.67  fof(f139,plain,(
% 1.28/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f138,f54])).
% 1.28/0.67  fof(f138,plain,(
% 1.28/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(resolution,[],[f72,f51])).
% 1.28/0.67  fof(f72,plain,(
% 1.28/0.67    ( ! [X0,X1] : (~v4_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f24])).
% 1.28/0.67  fof(f130,plain,(
% 1.28/0.67    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,X0)) )),
% 1.28/0.67    inference(forward_demodulation,[],[f129,f85])).
% 1.28/0.67  fof(f85,plain,(
% 1.28/0.67    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 1.28/0.67    inference(resolution,[],[f63,f54])).
% 1.28/0.67  fof(f63,plain,(
% 1.28/0.67    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f18])).
% 1.28/0.67  fof(f18,plain,(
% 1.28/0.67    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.28/0.67    inference(ennf_transformation,[],[f6])).
% 1.28/0.67  fof(f6,axiom,(
% 1.28/0.67    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.28/0.67  fof(f129,plain,(
% 1.28/0.67    ( ! [X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f128,f49])).
% 1.28/0.67  fof(f128,plain,(
% 1.28/0.67    ( ! [X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f127,f52])).
% 1.28/0.67  fof(f127,plain,(
% 1.28/0.67    ( ! [X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f126,f53])).
% 1.28/0.67  fof(f53,plain,(
% 1.28/0.67    v1_yellow_0(sK0)),
% 1.28/0.67    inference(cnf_transformation,[],[f38])).
% 1.28/0.67  fof(f126,plain,(
% 1.28/0.67    ( ! [X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f125,f54])).
% 1.28/0.67  fof(f125,plain,(
% 1.28/0.67    ( ! [X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f124,f61])).
% 1.28/0.67  fof(f61,plain,(
% 1.28/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f1])).
% 1.28/0.67  fof(f1,axiom,(
% 1.28/0.67    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.28/0.67  fof(f124,plain,(
% 1.28/0.67    ( ! [X0] : (~r1_yellow_0(sK0,X0) | ~r1_tarski(k1_xboole_0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.28/0.67    inference(resolution,[],[f123,f73])).
% 1.28/0.67  fof(f73,plain,(
% 1.28/0.67    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f26])).
% 1.28/0.67  fof(f26,plain,(
% 1.28/0.67    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.28/0.67    inference(flattening,[],[f25])).
% 1.28/0.67  fof(f25,plain,(
% 1.28/0.67    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.28/0.67    inference(ennf_transformation,[],[f9])).
% 1.28/0.67  fof(f9,axiom,(
% 1.28/0.67    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).
% 1.28/0.67  fof(f123,plain,(
% 1.28/0.67    ( ! [X0,X1] : (~r1_yellow_0(sK0,X1) | ~r1_yellow_0(sK0,X0) | ~r1_tarski(X1,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X0))) )),
% 1.28/0.67    inference(resolution,[],[f70,f54])).
% 1.28/0.67  fof(f70,plain,(
% 1.28/0.67    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) )),
% 1.28/0.67    inference(cnf_transformation,[],[f22])).
% 1.28/0.67  fof(f22,plain,(
% 1.28/0.67    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.28/0.67    inference(flattening,[],[f21])).
% 1.28/0.67  fof(f21,plain,(
% 1.28/0.67    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 1.28/0.67    inference(ennf_transformation,[],[f8])).
% 1.28/0.67  fof(f8,axiom,(
% 1.28/0.67    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).
% 1.28/0.67  fof(f195,plain,(
% 1.28/0.67    ( ! [X3] : (~r1_orders_2(sK0,k3_yellow_0(sK0),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,sK1) | u1_struct_0(sK0) = sK1) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f194,f58])).
% 1.28/0.67  fof(f194,plain,(
% 1.28/0.67    ( ! [X3] : (~r1_orders_2(sK0,k3_yellow_0(sK0),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,sK1) | u1_struct_0(sK0) = sK1) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f191,f57])).
% 1.28/0.67  fof(f57,plain,(
% 1.28/0.67    v13_waybel_0(sK1,sK0)),
% 1.28/0.67    inference(cnf_transformation,[],[f38])).
% 1.28/0.67  fof(f191,plain,(
% 1.28/0.67    ( ! [X3] : (~r1_orders_2(sK0,k3_yellow_0(sK0),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~v13_waybel_0(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,sK1) | u1_struct_0(sK0) = sK1) )),
% 1.28/0.67    inference(resolution,[],[f189,f92])).
% 1.28/0.67  fof(f92,plain,(
% 1.28/0.67    r2_hidden(k3_yellow_0(sK0),sK1) | u1_struct_0(sK0) = sK1),
% 1.28/0.67    inference(resolution,[],[f86,f60])).
% 1.28/0.67  fof(f60,plain,(
% 1.28/0.67    ~v1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.28/0.67    inference(cnf_transformation,[],[f38])).
% 1.28/0.67  fof(f86,plain,(
% 1.28/0.67    v1_subset_1(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1),
% 1.28/0.67    inference(resolution,[],[f81,f58])).
% 1.28/0.67  fof(f189,plain,(
% 1.28/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) )),
% 1.28/0.67    inference(resolution,[],[f188,f54])).
% 1.28/0.67  fof(f188,plain,(
% 1.28/0.67    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f64,f82])).
% 1.28/0.67  fof(f82,plain,(
% 1.28/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f33])).
% 1.28/0.67  fof(f33,plain,(
% 1.28/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.28/0.67    inference(flattening,[],[f32])).
% 1.28/0.67  fof(f32,plain,(
% 1.28/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.28/0.67    inference(ennf_transformation,[],[f5])).
% 1.28/0.67  fof(f5,axiom,(
% 1.28/0.67    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.28/0.67  fof(f64,plain,(
% 1.28/0.67    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f43])).
% 1.28/0.67  fof(f43,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.28/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).
% 1.28/0.67  fof(f41,plain,(
% 1.28/0.67    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f42,plain,(
% 1.28/0.67    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f40,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.28/0.67    inference(rectify,[],[f39])).
% 1.28/0.67  fof(f39,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.28/0.67    inference(nnf_transformation,[],[f20])).
% 1.28/0.67  fof(f20,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.28/0.67    inference(flattening,[],[f19])).
% 1.28/0.67  fof(f19,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.28/0.67    inference(ennf_transformation,[],[f10])).
% 1.28/0.67  fof(f10,axiom,(
% 1.28/0.67    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.28/0.67  fof(f59,plain,(
% 1.28/0.67    v1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.28/0.67    inference(cnf_transformation,[],[f38])).
% 1.28/0.67  fof(f238,plain,(
% 1.28/0.67    m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.28/0.67    inference(subsumption_resolution,[],[f230,f54])).
% 1.28/0.67  fof(f230,plain,(
% 1.28/0.67    m1_subset_1(k3_yellow_0(sK0),sK1) | ~l1_orders_2(sK0)),
% 1.28/0.67    inference(superposition,[],[f62,f210])).
% 1.28/0.67  fof(f62,plain,(
% 1.28/0.67    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f17])).
% 1.28/0.67  fof(f17,plain,(
% 1.28/0.67    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.28/0.67    inference(ennf_transformation,[],[f7])).
% 1.28/0.67  fof(f7,axiom,(
% 1.28/0.67    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.28/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.28/0.67  % SZS output end Proof for theBenchmark
% 1.28/0.67  % (28777)------------------------------
% 1.28/0.67  % (28777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.67  % (28777)Termination reason: Refutation
% 1.28/0.67  
% 1.28/0.67  % (28777)Memory used [KB]: 6396
% 1.28/0.67  % (28777)Time elapsed: 0.075 s
% 1.28/0.67  % (28777)------------------------------
% 1.28/0.67  % (28777)------------------------------
% 1.28/0.67  % (28606)Success in time 0.304 s
%------------------------------------------------------------------------------
