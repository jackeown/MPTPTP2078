%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  129 (1946 expanded)
%              Number of leaves         :   18 ( 489 expanded)
%              Depth                    :   35
%              Number of atoms          :  556 (19914 expanded)
%              Number of equality atoms :   36 ( 272 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f523,plain,(
    $false ),
    inference(subsumption_resolution,[],[f522,f456])).

fof(f456,plain,(
    m1_subset_1(k3_yellow_0(sK2),sK3) ),
    inference(backward_demodulation,[],[f116,f452])).

fof(f452,plain,(
    u1_struct_0(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f451,f144])).

fof(f144,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | u1_struct_0(sK2) = sK3 ),
    inference(resolution,[],[f62,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK6(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( r2_hidden(k3_yellow_0(sK2),sK3)
      | ~ v1_subset_1(sK3,u1_struct_0(sK2)) )
    & ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
      | v1_subset_1(sK3,u1_struct_0(sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v13_waybel_0(sK3,sK2)
    & ~ v1_xboole_0(sK3)
    & l1_orders_2(sK2)
    & v1_yellow_0(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f43,f42])).

fof(f42,plain,
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
          ( ( r2_hidden(k3_yellow_0(sK2),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK2)) )
          & ( ~ r2_hidden(k3_yellow_0(sK2),X1)
            | v1_subset_1(X1,u1_struct_0(sK2)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v13_waybel_0(X1,sK2)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK2)
      & v1_yellow_0(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK2),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK2)) )
        & ( ~ r2_hidden(k3_yellow_0(sK2),X1)
          | v1_subset_1(X1,u1_struct_0(sK2)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v13_waybel_0(X1,sK2)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK2),sK3)
        | ~ v1_subset_1(sK3,u1_struct_0(sK2)) )
      & ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
        | v1_subset_1(sK3,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v13_waybel_0(sK3,sK2)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f451,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | u1_struct_0(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f450,f429])).

fof(f429,plain,
    ( r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3))
    | u1_struct_0(sK2) = sK3 ),
    inference(resolution,[],[f390,f144])).

fof(f390,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3)) ),
    inference(subsumption_resolution,[],[f389,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f389,plain,
    ( r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3))
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f388,f55])).

fof(f55,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f388,plain,
    ( r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3))
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f387,f56])).

fof(f56,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f387,plain,
    ( r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3))
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f386,f57])).

fof(f57,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f386,plain,
    ( r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3))
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f384,f59])).

fof(f59,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f384,plain,
    ( r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3))
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f376,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f376,plain,(
    r1_orders_2(sK2,k3_yellow_0(sK2),k1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))) ),
    inference(resolution,[],[f375,f174])).

fof(f174,plain,(
    ! [X1] :
      ( ~ r1_yellow_0(sK2,X1)
      | r1_orders_2(sK2,k3_yellow_0(sK2),k1_yellow_0(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f173,f59])).

fof(f173,plain,(
    ! [X1] :
      ( r1_orders_2(sK2,k3_yellow_0(sK2),k1_yellow_0(sK2,X1))
      | ~ r1_yellow_0(sK2,X1)
      | ~ l1_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f172,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f172,plain,(
    ! [X1] :
      ( r1_orders_2(sK2,k3_yellow_0(sK2),k1_yellow_0(sK2,X1))
      | ~ r1_yellow_0(sK2,X1)
      | ~ r1_tarski(k1_xboole_0,X1)
      | ~ l1_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f169,f133])).

fof(f133,plain,(
    r1_yellow_0(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f132,f54])).

fof(f132,plain,
    ( r1_yellow_0(sK2,k1_xboole_0)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f131,f57])).

fof(f131,plain,
    ( r1_yellow_0(sK2,k1_xboole_0)
    | ~ v5_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f122,f58])).

fof(f58,plain,(
    v1_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f122,plain,
    ( r1_yellow_0(sK2,k1_xboole_0)
    | ~ v1_yellow_0(sK2)
    | ~ v5_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f59,f82])).

fof(f82,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f169,plain,(
    ! [X1] :
      ( r1_orders_2(sK2,k3_yellow_0(sK2),k1_yellow_0(sK2,X1))
      | ~ r1_yellow_0(sK2,X1)
      | ~ r1_yellow_0(sK2,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X1)
      | ~ l1_orders_2(sK2) ) ),
    inference(superposition,[],[f79,f117])).

fof(f117,plain,(
    k3_yellow_0(sK2) = k1_yellow_0(sK2,k1_xboole_0) ),
    inference(resolution,[],[f59,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f375,plain,(
    r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) ),
    inference(subsumption_resolution,[],[f374,f290])).

fof(f290,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK3)
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) ),
    inference(subsumption_resolution,[],[f280,f60])).

fof(f60,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f280,plain,
    ( v1_xboole_0(sK3)
    | r2_hidden(k3_yellow_0(sK2),sK3)
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) ),
    inference(superposition,[],[f157,f251])).

fof(f251,plain,
    ( u1_struct_0(sK2) = sK3
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) ),
    inference(subsumption_resolution,[],[f250,f54])).

fof(f250,plain,
    ( u1_struct_0(sK2) = sK3
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f249,f55])).

fof(f249,plain,
    ( u1_struct_0(sK2) = sK3
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f248,f56])).

fof(f248,plain,
    ( u1_struct_0(sK2) = sK3
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f247,f57])).

fof(f247,plain,
    ( u1_struct_0(sK2) = sK3
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f242,f59])).

fof(f242,plain,
    ( u1_struct_0(sK2) = sK3
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))
    | ~ l1_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f144,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f157,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(k3_yellow_0(sK2),u1_struct_0(sK2)) ),
    inference(resolution,[],[f116,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f374,plain,
    ( ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) ),
    inference(subsumption_resolution,[],[f272,f310])).

fof(f310,plain,
    ( ~ v1_subset_1(sK3,sK3)
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) ),
    inference(resolution,[],[f271,f89])).

fof(f89,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f271,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) ),
    inference(superposition,[],[f62,f251])).

fof(f272,plain,
    ( v1_subset_1(sK3,sK3)
    | ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) ),
    inference(superposition,[],[f63,f251])).

fof(f63,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(k3_yellow_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f450,plain,
    ( ~ r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3))
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | u1_struct_0(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f449,f177])).

fof(f177,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK3)
    | u1_struct_0(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f176,f62])).

fof(f176,plain,
    ( r2_hidden(k3_yellow_0(sK2),sK3)
    | u1_struct_0(sK2) = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f64,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f64,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(k3_yellow_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f449,plain,
    ( ~ r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3))
    | ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | u1_struct_0(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f448,f150])).

fof(f150,plain,(
    sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f148,f61])).

fof(f61,plain,(
    v13_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f148,plain,
    ( sP0(sK3,sK2)
    | ~ v13_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f147,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v13_waybel_0(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f147,plain,(
    sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f141,f59])).

fof(f141,plain,
    ( sP1(sK2,sK3)
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f62,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f23,f38,f37])).

fof(f37,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f448,plain,
    ( ~ r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3))
    | ~ r2_hidden(k3_yellow_0(sK2),sK3)
    | ~ m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ sP0(sK3,sK2)
    | u1_struct_0(sK2) = sK3 ),
    inference(resolution,[],[f155,f145])).

fof(f145,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3)
    | u1_struct_0(sK2) = sK3 ),
    inference(resolution,[],[f62,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK6(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f155,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_orders_2(sK2,k3_yellow_0(sK2),X0)
      | ~ r2_hidden(k3_yellow_0(sK2),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ sP0(X1,sK2) ) ),
    inference(resolution,[],[f116,f72])).

fof(f72,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X0)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X0)
          & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1))
          & r2_hidden(sK4(X0,X1),X0)
          & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))
          & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X4,X5)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f47,f49,f48])).

fof(f48,plain,(
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
            & r1_orders_2(X1,sK4(X0,X1),X3)
            & r2_hidden(sK4(X0,X1),X0)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r1_orders_2(X1,sK4(X0,X1),X3)
          & r2_hidden(sK4(X0,X1),X0)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(sK5(X0,X1),X0)
        & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1))
        & r2_hidden(sK4(X0,X1),X0)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f116,plain,(
    m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) ),
    inference(resolution,[],[f59,f68])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f522,plain,(
    ~ m1_subset_1(k3_yellow_0(sK2),sK3) ),
    inference(subsumption_resolution,[],[f520,f60])).

fof(f520,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(k3_yellow_0(sK2),sK3) ),
    inference(resolution,[],[f519,f83])).

fof(f519,plain,(
    ~ r2_hidden(k3_yellow_0(sK2),sK3) ),
    inference(subsumption_resolution,[],[f454,f509])).

fof(f509,plain,(
    ~ v1_subset_1(sK3,sK3) ),
    inference(resolution,[],[f453,f89])).

fof(f453,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK3)) ),
    inference(backward_demodulation,[],[f62,f452])).

fof(f454,plain,
    ( v1_subset_1(sK3,sK3)
    | ~ r2_hidden(k3_yellow_0(sK2),sK3) ),
    inference(backward_demodulation,[],[f63,f452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:49:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.43  % (27678)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.45  % (27678)Refutation not found, incomplete strategy% (27678)------------------------------
% 0.20/0.45  % (27678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (27694)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.46  % (27678)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (27678)Memory used [KB]: 10746
% 0.20/0.46  % (27678)Time elapsed: 0.070 s
% 0.20/0.46  % (27678)------------------------------
% 0.20/0.46  % (27678)------------------------------
% 0.20/0.46  % (27685)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.48  % (27685)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (27692)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f523,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f522,f456])).
% 0.20/0.49  fof(f456,plain,(
% 0.20/0.49    m1_subset_1(k3_yellow_0(sK2),sK3)),
% 0.20/0.49    inference(backward_demodulation,[],[f116,f452])).
% 0.20/0.49  fof(f452,plain,(
% 0.20/0.49    u1_struct_0(sK2) = sK3),
% 0.20/0.49    inference(subsumption_resolution,[],[f451,f144])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | u1_struct_0(sK2) = sK3),
% 0.20/0.49    inference(resolution,[],[f62,f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK6(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(flattening,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ((r2_hidden(k3_yellow_0(sK2),sK3) | ~v1_subset_1(sK3,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),sK3) | v1_subset_1(sK3,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(sK3,sK2) & ~v1_xboole_0(sK3)) & l1_orders_2(sK2) & v1_yellow_0(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f43,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK2),X1) | ~v1_subset_1(X1,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),X1) | v1_subset_1(X1,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(X1,sK2) & ~v1_xboole_0(X1)) & l1_orders_2(sK2) & v1_yellow_0(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ? [X1] : ((r2_hidden(k3_yellow_0(sK2),X1) | ~v1_subset_1(X1,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),X1) | v1_subset_1(X1,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(X1,sK2) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK2),sK3) | ~v1_subset_1(sK3,u1_struct_0(sK2))) & (~r2_hidden(k3_yellow_0(sK2),sK3) | v1_subset_1(sK3,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v13_waybel_0(sK3,sK2) & ~v1_xboole_0(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.49  fof(f15,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f14])).
% 0.20/0.49  fof(f14,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.20/0.49  fof(f451,plain,(
% 0.20/0.49    ~m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | u1_struct_0(sK2) = sK3),
% 0.20/0.49    inference(subsumption_resolution,[],[f450,f429])).
% 0.20/0.49  fof(f429,plain,(
% 0.20/0.49    r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3)) | u1_struct_0(sK2) = sK3),
% 0.20/0.49    inference(resolution,[],[f390,f144])).
% 0.20/0.49  fof(f390,plain,(
% 0.20/0.49    ~m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3))),
% 0.20/0.49    inference(subsumption_resolution,[],[f389,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ~v2_struct_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f389,plain,(
% 0.20/0.49    r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3)) | ~m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v2_struct_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f388,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    v3_orders_2(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f388,plain,(
% 0.20/0.49    r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3)) | ~m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f387,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    v4_orders_2(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f387,plain,(
% 0.20/0.49    r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3)) | ~m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f386,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    v5_orders_2(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f386,plain,(
% 0.20/0.49    r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3)) | ~m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f384,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    l1_orders_2(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f384,plain,(
% 0.20/0.49    r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3)) | ~m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.20/0.49    inference(superposition,[],[f376,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_waybel_0)).
% 0.20/0.49  fof(f376,plain,(
% 0.20/0.49    r1_orders_2(sK2,k3_yellow_0(sK2),k1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))))),
% 0.20/0.49    inference(resolution,[],[f375,f174])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ( ! [X1] : (~r1_yellow_0(sK2,X1) | r1_orders_2(sK2,k3_yellow_0(sK2),k1_yellow_0(sK2,X1))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f173,f59])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    ( ! [X1] : (r1_orders_2(sK2,k3_yellow_0(sK2),k1_yellow_0(sK2,X1)) | ~r1_yellow_0(sK2,X1) | ~l1_orders_2(sK2)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f172,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    ( ! [X1] : (r1_orders_2(sK2,k3_yellow_0(sK2),k1_yellow_0(sK2,X1)) | ~r1_yellow_0(sK2,X1) | ~r1_tarski(k1_xboole_0,X1) | ~l1_orders_2(sK2)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f169,f133])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    r1_yellow_0(sK2,k1_xboole_0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f132,f54])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    r1_yellow_0(sK2,k1_xboole_0) | v2_struct_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f131,f57])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    r1_yellow_0(sK2,k1_xboole_0) | ~v5_orders_2(sK2) | v2_struct_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f122,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    v1_yellow_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    r1_yellow_0(sK2,k1_xboole_0) | ~v1_yellow_0(sK2) | ~v5_orders_2(sK2) | v2_struct_0(sK2)),
% 0.20/0.49    inference(resolution,[],[f59,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    ( ! [X1] : (r1_orders_2(sK2,k3_yellow_0(sK2),k1_yellow_0(sK2,X1)) | ~r1_yellow_0(sK2,X1) | ~r1_yellow_0(sK2,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X1) | ~l1_orders_2(sK2)) )),
% 0.20/0.49    inference(superposition,[],[f79,f117])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    k3_yellow_0(sK2) = k1_yellow_0(sK2,k1_xboole_0)),
% 0.20/0.49    inference(resolution,[],[f59,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).
% 0.20/0.49  fof(f375,plain,(
% 0.20/0.49    r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f374,f290])).
% 0.20/0.49  fof(f290,plain,(
% 0.20/0.49    r2_hidden(k3_yellow_0(sK2),sK3) | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f280,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ~v1_xboole_0(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f280,plain,(
% 0.20/0.49    v1_xboole_0(sK3) | r2_hidden(k3_yellow_0(sK2),sK3) | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))),
% 0.20/0.49    inference(superposition,[],[f157,f251])).
% 0.20/0.49  fof(f251,plain,(
% 0.20/0.49    u1_struct_0(sK2) = sK3 | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f250,f54])).
% 0.20/0.49  fof(f250,plain,(
% 0.20/0.49    u1_struct_0(sK2) = sK3 | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) | v2_struct_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f249,f55])).
% 0.20/0.49  fof(f249,plain,(
% 0.20/0.49    u1_struct_0(sK2) = sK3 | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f248,f56])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    u1_struct_0(sK2) = sK3 | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f247,f57])).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    u1_struct_0(sK2) = sK3 | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f242,f59])).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    u1_struct_0(sK2) = sK3 | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3))) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.20/0.49    inference(resolution,[],[f144,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(k3_yellow_0(sK2),u1_struct_0(sK2))),
% 0.20/0.49    inference(resolution,[],[f116,f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.49  fof(f374,plain,(
% 0.20/0.49    ~r2_hidden(k3_yellow_0(sK2),sK3) | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f272,f310])).
% 0.20/0.49  fof(f310,plain,(
% 0.20/0.49    ~v1_subset_1(sK3,sK3) | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))),
% 0.20/0.49    inference(resolution,[],[f271,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(sK3)) | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))),
% 0.20/0.49    inference(superposition,[],[f62,f251])).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    v1_subset_1(sK3,sK3) | ~r2_hidden(k3_yellow_0(sK2),sK3) | r1_yellow_0(sK2,k5_waybel_0(sK2,sK6(u1_struct_0(sK2),sK3)))),
% 0.20/0.49    inference(superposition,[],[f63,f251])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    v1_subset_1(sK3,u1_struct_0(sK2)) | ~r2_hidden(k3_yellow_0(sK2),sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f450,plain,(
% 0.20/0.49    ~r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3)) | ~m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | u1_struct_0(sK2) = sK3),
% 0.20/0.49    inference(subsumption_resolution,[],[f449,f177])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    r2_hidden(k3_yellow_0(sK2),sK3) | u1_struct_0(sK2) = sK3),
% 0.20/0.49    inference(subsumption_resolution,[],[f176,f62])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    r2_hidden(k3_yellow_0(sK2),sK3) | u1_struct_0(sK2) = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.49    inference(resolution,[],[f64,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f53])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ~v1_subset_1(sK3,u1_struct_0(sK2)) | r2_hidden(k3_yellow_0(sK2),sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f449,plain,(
% 0.20/0.49    ~r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3)) | ~r2_hidden(k3_yellow_0(sK2),sK3) | ~m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | u1_struct_0(sK2) = sK3),
% 0.20/0.49    inference(subsumption_resolution,[],[f448,f150])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    sP0(sK3,sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f148,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    v13_waybel_0(sK3,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    sP0(sK3,sK2) | ~v13_waybel_0(sK3,sK2)),
% 0.20/0.49    inference(resolution,[],[f147,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP0(X1,X0) | ~v13_waybel_0(X1,X0) | ~sP1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ! [X0,X1] : (((v13_waybel_0(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v13_waybel_0(X1,X0))) | ~sP1(X0,X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1] : ((v13_waybel_0(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    sP1(sK2,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f141,f59])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    sP1(sK2,sK3) | ~l1_orders_2(sK2)),
% 0.20/0.49    inference(resolution,[],[f62,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(definition_folding,[],[f23,f38,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.20/0.49  fof(f448,plain,(
% 0.20/0.49    ~r1_orders_2(sK2,k3_yellow_0(sK2),sK6(u1_struct_0(sK2),sK3)) | ~r2_hidden(k3_yellow_0(sK2),sK3) | ~m1_subset_1(sK6(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~sP0(sK3,sK2) | u1_struct_0(sK2) = sK3),
% 0.20/0.49    inference(resolution,[],[f155,f145])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ~r2_hidden(sK6(u1_struct_0(sK2),sK3),sK3) | u1_struct_0(sK2) = sK3),
% 0.20/0.49    inference(resolution,[],[f62,f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK6(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_orders_2(sK2,k3_yellow_0(sK2),X0) | ~r2_hidden(k3_yellow_0(sK2),X1) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~sP0(X1,sK2)) )),
% 0.20/0.49    inference(resolution,[],[f116,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK5(X0,X1),X0) & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f47,f49,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1))) => (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK5(X0,X1),X0) & r1_orders_2(X1,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X0) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_orders_2(X1,X2,X3) & r2_hidden(X2,X0) & m1_subset_1(X3,u1_struct_0(X1))) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,X0) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP0(X1,X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f37])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2))),
% 0.20/0.49    inference(resolution,[],[f59,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.20/0.49  fof(f522,plain,(
% 0.20/0.49    ~m1_subset_1(k3_yellow_0(sK2),sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f520,f60])).
% 0.20/0.49  fof(f520,plain,(
% 0.20/0.49    v1_xboole_0(sK3) | ~m1_subset_1(k3_yellow_0(sK2),sK3)),
% 0.20/0.49    inference(resolution,[],[f519,f83])).
% 0.20/0.49  fof(f519,plain,(
% 0.20/0.49    ~r2_hidden(k3_yellow_0(sK2),sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f454,f509])).
% 0.20/0.49  fof(f509,plain,(
% 0.20/0.49    ~v1_subset_1(sK3,sK3)),
% 0.20/0.49    inference(resolution,[],[f453,f89])).
% 0.20/0.49  fof(f453,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(sK3))),
% 0.20/0.49    inference(backward_demodulation,[],[f62,f452])).
% 0.20/0.49  fof(f454,plain,(
% 0.20/0.49    v1_subset_1(sK3,sK3) | ~r2_hidden(k3_yellow_0(sK2),sK3)),
% 0.20/0.49    inference(backward_demodulation,[],[f63,f452])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (27685)------------------------------
% 0.20/0.49  % (27685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (27685)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (27685)Memory used [KB]: 1791
% 0.20/0.49  % (27685)Time elapsed: 0.099 s
% 0.20/0.49  % (27685)------------------------------
% 0.20/0.49  % (27685)------------------------------
% 0.20/0.49  % (27676)Success in time 0.132 s
%------------------------------------------------------------------------------
