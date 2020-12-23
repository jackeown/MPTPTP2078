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
% DateTime   : Thu Dec  3 13:22:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 991 expanded)
%              Number of leaves         :   15 ( 302 expanded)
%              Depth                    :   41
%              Number of atoms          :  749 (8633 expanded)
%              Number of equality atoms :   76 ( 933 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f410,plain,(
    $false ),
    inference(subsumption_resolution,[],[f397,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f397,plain,(
    ~ r1_tarski(k11_yellow_6(sK0,sK1),k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f390,f386])).

fof(f386,plain,(
    ~ r1_tarski(k4_yellow_6(sK0,sK1),k11_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f385,f51])).

fof(f51,plain,(
    k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & v1_yellow_6(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
            & l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1)
          & l1_waybel_0(X1,sK0)
          & v1_yellow_6(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1)
        & l1_waybel_0(X1,sK0)
        & v1_yellow_6(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1)
      & l1_waybel_0(sK1,sK0)
      & v1_yellow_6(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_6)).

fof(f385,plain,
    ( k11_yellow_6(sK0,sK1) = k4_yellow_6(sK0,sK1)
    | ~ r1_tarski(k4_yellow_6(sK0,sK1),k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f376,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f376,plain,(
    r1_tarski(k11_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f367,f74])).

fof(f367,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_yellow_6(sK0,sK1),X0)
      | r1_tarski(k11_yellow_6(sK0,sK1),X0) ) ),
    inference(resolution,[],[f305,f77])).

fof(f77,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f305,plain,(
    ! [X0] :
      ( r2_hidden(k11_yellow_6(sK0,sK1),k1_zfmisc_1(X0))
      | ~ r1_tarski(k4_yellow_6(sK0,sK1),X0) ) ),
    inference(resolution,[],[f277,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f277,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_yellow_6(sK0,sK1),X0)
      | r2_hidden(k11_yellow_6(sK0,sK1),X0) ) ),
    inference(resolution,[],[f255,f177])).

fof(f177,plain,(
    ! [X2] :
      ( r1_tarski(k10_yellow_6(sK0,sK1),X2)
      | ~ r2_hidden(k4_yellow_6(sK0,sK1),X2) ) ),
    inference(superposition,[],[f72,f167])).

fof(f167,plain,(
    k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f165,f78])).

fof(f78,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f71,f74])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f165,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(k4_yellow_6(sK0,sK1)))
      | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f162,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f162,plain,
    ( v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f161,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f161,plain,
    ( v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f160,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f160,plain,
    ( v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f159,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f159,plain,
    ( v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f158,plain,
    ( v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f47])).

fof(f47,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f157,plain,
    ( v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1))
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f156,f48])).

fof(f48,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f156,plain,
    ( v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1))
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f155,f49])).

fof(f49,plain,(
    v1_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f155,plain,
    ( v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1))
    | ~ v1_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f144,f50])).

fof(f50,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f144,plain,
    ( v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f142,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).

fof(f142,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | v1_xboole_0(k1_tarski(X0))
      | k1_tarski(X0) = k10_yellow_6(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f136,f60])).

fof(f136,plain,(
    ! [X0] :
      ( k1_tarski(X0) = k10_yellow_6(sK0,sK1)
      | v1_xboole_0(k10_yellow_6(sK0,sK1))
      | v1_xboole_0(k1_tarski(X0))
      | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f134,f72])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_yellow_6(sK0,sK1))
      | k10_yellow_6(sK0,sK1) = X0
      | v1_xboole_0(k10_yellow_6(sK0,sK1))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f133,f48])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK1)
      | ~ r1_tarski(X0,k10_yellow_6(sK0,sK1))
      | k10_yellow_6(sK0,sK1) = X0
      | v1_xboole_0(k10_yellow_6(sK0,sK1))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f132,f46])).

fof(f132,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ r1_tarski(X0,k10_yellow_6(sK0,sK1))
      | k10_yellow_6(sK0,sK1) = X0
      | v1_xboole_0(k10_yellow_6(sK0,sK1))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f131,f47])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ r1_tarski(X0,k10_yellow_6(sK0,sK1))
      | k10_yellow_6(sK0,sK1) = X0
      | v1_xboole_0(k10_yellow_6(sK0,sK1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f130,f50])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v7_waybel_0(X0)
      | ~ r1_tarski(X1,k10_yellow_6(sK0,X0))
      | k10_yellow_6(sK0,X0) = X1
      | v1_xboole_0(k10_yellow_6(sK0,X0))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f129,f42])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(sK0)
      | ~ r1_tarski(X1,k10_yellow_6(sK0,X0))
      | k10_yellow_6(sK0,X0) = X1
      | v1_xboole_0(k10_yellow_6(sK0,X0))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f128,f43])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r1_tarski(X1,k10_yellow_6(sK0,X0))
      | k10_yellow_6(sK0,X0) = X1
      | v1_xboole_0(k10_yellow_6(sK0,X0))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f127,f45])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r1_tarski(X1,k10_yellow_6(sK0,X0))
      | k10_yellow_6(sK0,X0) = X1
      | v1_xboole_0(k10_yellow_6(sK0,X0))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f104,f44])).

fof(f44,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_pre_topc(X1)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_waybel_0(X0,X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r1_tarski(X2,k10_yellow_6(X1,X0))
      | k10_yellow_6(X1,X0) = X2
      | v1_xboole_0(k10_yellow_6(X1,X0))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f63,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => v1_zfmisc_1(k10_yellow_6(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_yellow_6)).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f255,plain,(
    ! [X1] :
      ( ~ r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | r2_hidden(k11_yellow_6(sK0,sK1),X1) ) ),
    inference(superposition,[],[f71,f247])).

fof(f247,plain,(
    k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f241,f78])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1)))
      | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f240,f42])).

fof(f240,plain,(
    ! [X0] :
      ( k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
      | ~ r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f239,f43])).

fof(f239,plain,(
    ! [X0] :
      ( k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
      | ~ r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f238,f45])).

fof(f238,plain,(
    ! [X0] :
      ( k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
      | ~ r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f237,f50])).

fof(f237,plain,(
    ! [X0] :
      ( k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
      | ~ r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1)))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f236,f49])).

fof(f236,plain,(
    ! [X0] :
      ( k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
      | ~ r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1)))
      | ~ v1_yellow_6(sK1,sK0)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f203,f103])).

fof(f103,plain,(
    ! [X0] :
      ( v3_yellow_6(sK1,X0)
      | ~ v1_yellow_6(sK1,X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f102,f46])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_yellow_6(sK1,X0)
      | v3_yellow_6(sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f101,f47])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_yellow_6(sK1,X0)
      | v3_yellow_6(sK1,X0)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f58,f48])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v1_yellow_6(X1,X0)
      | v3_yellow_6(X1,X0)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( ( v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v3_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_6)).

fof(f203,plain,(
    ! [X0] :
      ( ~ v3_yellow_6(sK1,sK0)
      | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
      | ~ r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1))) ) ),
    inference(resolution,[],[f154,f60])).

fof(f154,plain,
    ( v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
    | ~ v3_yellow_6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f153,f42])).

fof(f153,plain,
    ( v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
    | ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f43])).

fof(f152,plain,
    ( v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f44])).

fof(f151,plain,
    ( v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f150,f45])).

fof(f150,plain,
    ( v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f46])).

fof(f149,plain,
    ( v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
    | ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f47])).

fof(f148,plain,
    ( v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f147,f48])).

fof(f147,plain,
    ( v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f143,f50])).

fof(f143,plain,
    ( v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1)))
    | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f142,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(k11_yellow_6(X0,X1),k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(k11_yellow_6(X0,X1),k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f73,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v3_yellow_6(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | r2_hidden(k11_yellow_6(X0,X1),k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | k11_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k11_yellow_6(X0,X1) = X2
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
                & ( r2_hidden(X2,k10_yellow_6(X0,X1))
                  | k11_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_yellow_6)).

fof(f390,plain,(
    ! [X1] :
      ( r1_tarski(k4_yellow_6(sK0,sK1),X1)
      | ~ r1_tarski(k11_yellow_6(sK0,sK1),X1) ) ),
    inference(resolution,[],[f315,f76])).

fof(f315,plain,(
    ! [X1] :
      ( ~ r2_hidden(k11_yellow_6(sK0,sK1),k1_zfmisc_1(X1))
      | r1_tarski(k4_yellow_6(sK0,sK1),X1) ) ),
    inference(resolution,[],[f282,f77])).

fof(f282,plain,(
    ! [X1] :
      ( r2_hidden(k4_yellow_6(sK0,sK1),X1)
      | ~ r2_hidden(k11_yellow_6(sK0,sK1),X1) ) ),
    inference(resolution,[],[f256,f176])).

fof(f176,plain,(
    ! [X1] :
      ( ~ r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | r2_hidden(k4_yellow_6(sK0,sK1),X1) ) ),
    inference(superposition,[],[f71,f167])).

fof(f256,plain,(
    ! [X2] :
      ( r1_tarski(k10_yellow_6(sK0,sK1),X2)
      | ~ r2_hidden(k11_yellow_6(sK0,sK1),X2) ) ),
    inference(superposition,[],[f72,f247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (3354)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.46  % (3346)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.47  % (3354)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f410,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f397,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(flattening,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f397,plain,(
% 0.21/0.48    ~r1_tarski(k11_yellow_6(sK0,sK1),k11_yellow_6(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f390,f386])).
% 0.21/0.48  fof(f386,plain,(
% 0.21/0.48    ~r1_tarski(k4_yellow_6(sK0,sK1),k11_yellow_6(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f385,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    (k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1) & l1_waybel_0(sK1,sK0) & v1_yellow_6(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f28,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1) & l1_waybel_0(X1,sK0) & v1_yellow_6(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ? [X1] : (k11_yellow_6(sK0,X1) != k4_yellow_6(sK0,X1) & l1_waybel_0(X1,sK0) & v1_yellow_6(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1) & l1_waybel_0(sK1,sK0) & v1_yellow_6(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & (l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_6)).
% 0.21/0.48  fof(f385,plain,(
% 0.21/0.48    k11_yellow_6(sK0,sK1) = k4_yellow_6(sK0,sK1) | ~r1_tarski(k4_yellow_6(sK0,sK1),k11_yellow_6(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f376,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    r1_tarski(k11_yellow_6(sK0,sK1),k4_yellow_6(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f367,f74])).
% 0.21/0.48  fof(f367,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k4_yellow_6(sK0,sK1),X0) | r1_tarski(k11_yellow_6(sK0,sK1),X0)) )),
% 0.21/0.48    inference(resolution,[],[f305,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.48    inference(rectify,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(k11_yellow_6(sK0,sK1),k1_zfmisc_1(X0)) | ~r1_tarski(k4_yellow_6(sK0,sK1),X0)) )),
% 0.21/0.48    inference(resolution,[],[f277,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(k4_yellow_6(sK0,sK1),X0) | r2_hidden(k11_yellow_6(sK0,sK1),X0)) )),
% 0.21/0.48    inference(resolution,[],[f255,f177])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ( ! [X2] : (r1_tarski(k10_yellow_6(sK0,sK1),X2) | ~r2_hidden(k4_yellow_6(sK0,sK1),X2)) )),
% 0.21/0.48    inference(superposition,[],[f72,f167])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f165,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.21/0.48    inference(resolution,[],[f71,f74])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_tarski(k4_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1))) )),
% 0.21/0.48    inference(resolution,[],[f162,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(rectify,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f161,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f160,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f159,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f158,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ~v2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f157,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    v4_orders_2(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f156,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    v7_waybel_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f155,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    v1_yellow_6(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1)) | ~v1_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f144,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    l1_waybel_0(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k4_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k4_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v1_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f142,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | v1_xboole_0(k1_tarski(X0)) | k1_tarski(X0) = k10_yellow_6(sK0,sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f136,f60])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X0] : (k1_tarski(X0) = k10_yellow_6(sK0,sK1) | v1_xboole_0(k10_yellow_6(sK0,sK1)) | v1_xboole_0(k1_tarski(X0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK1))) )),
% 0.21/0.48    inference(resolution,[],[f134,f72])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k10_yellow_6(sK0,sK1)) | k10_yellow_6(sK0,sK1) = X0 | v1_xboole_0(k10_yellow_6(sK0,sK1)) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f48])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X0] : (~v7_waybel_0(sK1) | ~r1_tarski(X0,k10_yellow_6(sK0,sK1)) | k10_yellow_6(sK0,sK1) = X0 | v1_xboole_0(k10_yellow_6(sK0,sK1)) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f132,f46])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ( ! [X0] : (v2_struct_0(sK1) | ~v7_waybel_0(sK1) | ~r1_tarski(X0,k10_yellow_6(sK0,sK1)) | k10_yellow_6(sK0,sK1) = X0 | v1_xboole_0(k10_yellow_6(sK0,sK1)) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f131,f47])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ( ! [X0] : (~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v7_waybel_0(sK1) | ~r1_tarski(X0,k10_yellow_6(sK0,sK1)) | k10_yellow_6(sK0,sK1) = X0 | v1_xboole_0(k10_yellow_6(sK0,sK1)) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f130,f50])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v7_waybel_0(X0) | ~r1_tarski(X1,k10_yellow_6(sK0,X0)) | k10_yellow_6(sK0,X0) = X1 | v1_xboole_0(k10_yellow_6(sK0,X0)) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f129,f42])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | v2_struct_0(sK0) | ~r1_tarski(X1,k10_yellow_6(sK0,X0)) | k10_yellow_6(sK0,X0) = X1 | v1_xboole_0(k10_yellow_6(sK0,X0)) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f128,f43])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(X1,k10_yellow_6(sK0,X0)) | k10_yellow_6(sK0,X0) = X1 | v1_xboole_0(k10_yellow_6(sK0,X0)) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f45])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~l1_waybel_0(X0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(X1,k10_yellow_6(sK0,X0)) | k10_yellow_6(sK0,X0) = X1 | v1_xboole_0(k10_yellow_6(sK0,X0)) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(resolution,[],[f104,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    v8_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v8_pre_topc(X1) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~l1_waybel_0(X0,X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r1_tarski(X2,k10_yellow_6(X1,X0)) | k10_yellow_6(X1,X0) = X2 | v1_xboole_0(k10_yellow_6(X1,X0)) | v1_xboole_0(X2)) )),
% 0.21/0.48    inference(resolution,[],[f63,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_zfmisc_1(k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_zfmisc_1(k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_zfmisc_1(k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => v1_zfmisc_1(k10_yellow_6(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_yellow_6)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(k10_yellow_6(sK0,sK1),X1) | r2_hidden(k11_yellow_6(sK0,sK1),X1)) )),
% 0.21/0.48    inference(superposition,[],[f71,f247])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f241,f78])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f240,f42])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ( ! [X0] : (k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1))) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f239,f43])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    ( ! [X0] : (k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f238,f45])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    ( ! [X0] : (k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f237,f50])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    ( ! [X0] : (k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1))) | ~l1_waybel_0(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f236,f49])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ( ! [X0] : (k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1))) | ~v1_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f203,f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0] : (v3_yellow_6(sK1,X0) | ~v1_yellow_6(sK1,X0) | ~l1_waybel_0(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f102,f46])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_yellow_6(sK1,X0) | v3_yellow_6(sK1,X0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f101,f47])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_yellow_6(sK1,X0) | v3_yellow_6(sK1,X0) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f58,f48])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v7_waybel_0(X1) | ~v1_yellow_6(X1,X0) | v3_yellow_6(X1,X0) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | (~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_waybel_0(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => ((v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_6)).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_yellow_6(sK1,sK0) | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~r2_hidden(X0,k1_tarski(k11_yellow_6(sK0,sK1)))) )),
% 0.21/0.48    inference(resolution,[],[f154,f60])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~v3_yellow_6(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f153,f42])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f152,f43])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f151,f44])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~v3_yellow_6(sK1,sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f150,f45])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~v3_yellow_6(sK1,sK0) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f46])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f47])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~v3_yellow_6(sK1,sK0) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f147,f48])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f143,f50])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    v1_xboole_0(k1_tarski(k11_yellow_6(sK0,sK1))) | k10_yellow_6(sK0,sK1) = k1_tarski(k11_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f142,f106])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(k11_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(k11_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f73,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | r2_hidden(k11_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | k11_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((k11_yellow_6(X0,X1) = X2 | ~r2_hidden(X2,k10_yellow_6(X0,X1))) & (r2_hidden(X2,k10_yellow_6(X0,X1)) | k11_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_yellow_6)).
% 0.21/0.48  fof(f390,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(k4_yellow_6(sK0,sK1),X1) | ~r1_tarski(k11_yellow_6(sK0,sK1),X1)) )),
% 0.21/0.48    inference(resolution,[],[f315,f76])).
% 0.21/0.48  fof(f315,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_hidden(k11_yellow_6(sK0,sK1),k1_zfmisc_1(X1)) | r1_tarski(k4_yellow_6(sK0,sK1),X1)) )),
% 0.21/0.48    inference(resolution,[],[f282,f77])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    ( ! [X1] : (r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~r2_hidden(k11_yellow_6(sK0,sK1),X1)) )),
% 0.21/0.48    inference(resolution,[],[f256,f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(k10_yellow_6(sK0,sK1),X1) | r2_hidden(k4_yellow_6(sK0,sK1),X1)) )),
% 0.21/0.48    inference(superposition,[],[f71,f167])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ( ! [X2] : (r1_tarski(k10_yellow_6(sK0,sK1),X2) | ~r2_hidden(k11_yellow_6(sK0,sK1),X2)) )),
% 0.21/0.48    inference(superposition,[],[f72,f247])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (3354)------------------------------
% 0.21/0.48  % (3354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3354)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (3354)Memory used [KB]: 1791
% 0.21/0.48  % (3354)Time elapsed: 0.070 s
% 0.21/0.48  % (3354)------------------------------
% 0.21/0.48  % (3354)------------------------------
% 0.21/0.49  % (3337)Success in time 0.127 s
%------------------------------------------------------------------------------
