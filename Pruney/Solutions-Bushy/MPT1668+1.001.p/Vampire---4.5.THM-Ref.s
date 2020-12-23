%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1668+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:18 EST 2020

% Result     : Theorem 3.74s
% Output     : Refutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  229 (34374 expanded)
%              Number of leaves         :   22 (10013 expanded)
%              Depth                    :   67
%              Number of atoms          : 1136 (373739 expanded)
%              Number of equality atoms :   67 (48599 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2486,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2479,f2058])).

fof(f2058,plain,(
    m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f2033,f112])).

fof(f112,plain,(
    r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f103,f73])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ! [X2] :
          ( k5_waybel_0(sK2,X2) != sK3
          | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
      | ~ v14_waybel_0(sK3,sK2) )
    & ( ( sK3 = k5_waybel_0(sK2,sK4)
        & m1_subset_1(sK4,u1_struct_0(sK2)) )
      | v14_waybel_0(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v12_waybel_0(sK3,sK2)
    & v1_waybel_0(sK3,sK2)
    & ~ v1_xboole_0(sK3)
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ! [X2] :
                  ( k5_waybel_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) )
            & ( ? [X3] :
                  ( k5_waybel_0(X0,X3) = X1
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | v14_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(sK2,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
            | ~ v14_waybel_0(X1,sK2) )
          & ( ? [X3] :
                ( k5_waybel_0(sK2,X3) = X1
                & m1_subset_1(X3,u1_struct_0(sK2)) )
            | v14_waybel_0(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v12_waybel_0(X1,sK2)
          & v1_waybel_0(X1,sK2)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ( ! [X2] :
              ( k5_waybel_0(sK2,X2) != X1
              | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
          | ~ v14_waybel_0(X1,sK2) )
        & ( ? [X3] :
              ( k5_waybel_0(sK2,X3) = X1
              & m1_subset_1(X3,u1_struct_0(sK2)) )
          | v14_waybel_0(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v12_waybel_0(X1,sK2)
        & v1_waybel_0(X1,sK2)
        & ~ v1_xboole_0(X1) )
   => ( ( ! [X2] :
            ( k5_waybel_0(sK2,X2) != sK3
            | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
        | ~ v14_waybel_0(sK3,sK2) )
      & ( ? [X3] :
            ( k5_waybel_0(sK2,X3) = sK3
            & m1_subset_1(X3,u1_struct_0(sK2)) )
        | v14_waybel_0(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v12_waybel_0(sK3,sK2)
      & v1_waybel_0(sK3,sK2)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( k5_waybel_0(sK2,X3) = sK3
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( sK3 = k5_waybel_0(sK2,sK4)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(X0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v14_waybel_0(X1,X0) )
          & ( ? [X3] :
                ( k5_waybel_0(X0,X3) = X1
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | v14_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(X0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v14_waybel_0(X1,X0) )
          & ( ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | v14_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(X0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v14_waybel_0(X1,X0) )
          & ( ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | v14_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v14_waybel_0(X1,X0)
          <~> ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v14_waybel_0(X1,X0)
          <~> ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v14_waybel_0(X1,X0)
            <=> ? [X2] :
                  ( k5_waybel_0(X0,X2) = X1
                  & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_waybel_0)).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2033,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,X0)
      | m1_subset_1(sK8(sK2,sK3),X0) ) ),
    inference(subsumption_resolution,[],[f1978,f2029])).

fof(f2029,plain,(
    ~ r2_hidden(sK4,sK3) ),
    inference(resolution,[],[f2011,f131])).

fof(f131,plain,(
    ! [X3] :
      ( m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r2_hidden(X3,sK3) ) ),
    inference(resolution,[],[f108,f73])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f2011,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f2010,f1971])).

fof(f1971,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,sK3) ),
    inference(resolution,[],[f1939,f1882])).

fof(f1882,plain,
    ( v14_waybel_0(sK3,sK2)
    | r2_hidden(sK4,sK3) ),
    inference(backward_demodulation,[],[f462,f1881])).

fof(f1881,plain,(
    sK3 = k5_waybel_0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f1880,f695])).

fof(f695,plain,
    ( m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2))
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(resolution,[],[f693,f112])).

fof(f693,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,X0)
      | m1_subset_1(sK8(sK2,sK3),X0)
      | sK3 = k5_waybel_0(sK2,sK4) ) ),
    inference(resolution,[],[f692,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f108,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f692,plain,
    ( r2_hidden(sK8(sK2,sK3),sK3)
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f691,f70])).

fof(f70,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f691,plain,
    ( v1_xboole_0(sK3)
    | r2_hidden(sK8(sK2,sK3),sK3)
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f690,f71])).

fof(f71,plain,(
    v1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f690,plain,
    ( ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_hidden(sK8(sK2,sK3),sK3)
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f689,f72])).

fof(f72,plain,(
    v12_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f689,plain,
    ( ~ v12_waybel_0(sK3,sK2)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_hidden(sK8(sK2,sK3),sK3)
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f688,f73])).

fof(f688,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v12_waybel_0(sK3,sK2)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_hidden(sK8(sK2,sK3),sK3)
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(resolution,[],[f494,f75])).

fof(f75,plain,
    ( v14_waybel_0(sK3,sK2)
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f494,plain,(
    ! [X0] :
      ( ~ v14_waybel_0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | r2_hidden(sK8(sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f493,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f493,plain,(
    ! [X0] :
      ( ~ v14_waybel_0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | r2_hidden(sK8(sK2,X0),X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f492,f67])).

fof(f67,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f492,plain,(
    ! [X0] :
      ( ~ v14_waybel_0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | r2_hidden(sK8(sK2,X0),X0)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f491,f69])).

fof(f69,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f491,plain,(
    ! [X0] :
      ( ~ v14_waybel_0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK2)
      | r2_hidden(sK8(sK2,X0),X0)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f91,f68])).

fof(f68,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ v14_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | r2_hidden(sK8(X0,X1),X1)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_waybel_0(X1,X0)
              | ! [X2] :
                  ( ~ r2_lattice3(X0,X1,X2)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ( r2_lattice3(X0,X1,sK8(X0,X1))
                & r2_hidden(sK8(X0,X1),X1)
                & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_lattice3(X0,X1,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( r2_lattice3(X0,X1,sK8(X0,X1))
        & r2_hidden(sK8(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_waybel_0(X1,X0)
              | ! [X2] :
                  ( ~ r2_lattice3(X0,X1,X2)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ? [X3] :
                  ( r2_lattice3(X0,X1,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_waybel_0(X1,X0)
              | ! [X2] :
                  ( ~ r2_lattice3(X0,X1,X2)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ? [X2] :
                  ( r2_lattice3(X0,X1,X2)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( r2_lattice3(X0,X1,X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( r2_lattice3(X0,X1,X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( r2_lattice3(X0,X1,X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_waybel_0)).

fof(f1880,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2))
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f1856,f75])).

fof(f1856,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2))
    | ~ v14_waybel_0(sK3,sK2)
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(trivial_inequality_removal,[],[f1803])).

fof(f1803,plain,
    ( sK3 != sK3
    | ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2))
    | ~ v14_waybel_0(sK3,sK2)
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(superposition,[],[f76,f1643])).

fof(f1643,plain,
    ( sK3 = k5_waybel_0(sK2,sK8(sK2,sK3))
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f819,f1628])).

fof(f1628,plain,
    ( r1_tarski(k5_waybel_0(sK2,sK8(sK2,sK3)),sK3)
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(resolution,[],[f1617,f692])).

fof(f1617,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3)
      | r1_tarski(k5_waybel_0(sK2,X2),sK3) ) ),
    inference(duplicate_literal_removal,[],[f1614])).

fof(f1614,plain,(
    ! [X2] :
      ( r1_tarski(k5_waybel_0(sK2,X2),sK3)
      | ~ r2_hidden(X2,sK3)
      | r1_tarski(k5_waybel_0(sK2,X2),sK3) ) ),
    inference(resolution,[],[f1610,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f61,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1610,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(k5_waybel_0(sK2,X0),X1),sK3)
      | r1_tarski(k5_waybel_0(sK2,X0),X1)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f1609,f131])).

fof(f1609,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | r1_tarski(k5_waybel_0(sK2,X0),X1)
      | r2_hidden(sK9(k5_waybel_0(sK2,X0),X1),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f1605])).

fof(f1605,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | r1_tarski(k5_waybel_0(sK2,X0),X1)
      | r2_hidden(sK9(k5_waybel_0(sK2,X0),X1),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tarski(k5_waybel_0(sK2,X0),X1) ) ),
    inference(resolution,[],[f389,f201])).

fof(f201,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK9(k5_waybel_0(sK2,X2),X3),u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r1_tarski(k5_waybel_0(sK2,X2),X3) ) ),
    inference(resolution,[],[f190,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f190,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k5_waybel_0(sK2,X1))
      | m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f188,f108])).

fof(f188,plain,(
    ! [X0] :
      ( m1_subset_1(k5_waybel_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f187,f66])).

fof(f187,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | m1_subset_1(k5_waybel_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f96,f69])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f389,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK9(k5_waybel_0(sK2,X0),X1),u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK3)
      | r1_tarski(k5_waybel_0(sK2,X0),X1)
      | r2_hidden(sK9(k5_waybel_0(sK2,X0),X1),sK3) ) ),
    inference(subsumption_resolution,[],[f388,f131])).

fof(f388,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tarski(k5_waybel_0(sK2,X0),X1)
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(sK9(k5_waybel_0(sK2,X0),X1),u1_struct_0(sK2))
      | r2_hidden(sK9(k5_waybel_0(sK2,X0),X1),sK3) ) ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tarski(k5_waybel_0(sK2,X0),X1)
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(sK9(k5_waybel_0(sK2,X0),X1),u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_hidden(sK9(k5_waybel_0(sK2,X0),X1),sK3) ) ),
    inference(resolution,[],[f378,f287])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f79,f125])).

fof(f125,plain,(
    sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f124,f72])).

fof(f124,plain,
    ( ~ v12_waybel_0(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(resolution,[],[f122,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v12_waybel_0(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v12_waybel_0(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v12_waybel_0(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v12_waybel_0(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f122,plain,(
    sP1(sK2,sK3) ),
    inference(resolution,[],[f120,f73])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f85,f69])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f17,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r1_orders_2(X0,X3,X2)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
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
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_waybel_0)).

fof(f79,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_orders_2(X1,X5,X4)
      | ~ r2_hidden(X4,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r2_hidden(X5,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X0)
          & r1_orders_2(X1,sK6(X0,X1),sK5(X0,X1))
          & r2_hidden(sK5(X0,X1),X0)
          & m1_subset_1(sK6(X0,X1),u1_struct_0(X1))
          & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X5,X4)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f45,f47,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r1_orders_2(X1,X3,X2)
              & r2_hidden(X2,X0)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r1_orders_2(X1,X3,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),X0)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r1_orders_2(X1,X3,sK5(X0,X1))
          & r2_hidden(sK5(X0,X1),X0)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(sK6(X0,X1),X0)
        & r1_orders_2(X1,sK6(X0,X1),sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r1_orders_2(X1,X3,X2)
                & r2_hidden(X2,X0)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_orders_2(X1,X5,X4)
                | ~ r2_hidden(X4,X0)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r1_orders_2(X0,X3,X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f378,plain,(
    ! [X8,X9] :
      ( r1_orders_2(sK2,sK9(k5_waybel_0(sK2,X8),X9),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK2))
      | r1_tarski(k5_waybel_0(sK2,X8),X9) ) ),
    inference(resolution,[],[f374,f101])).

fof(f374,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k5_waybel_0(sK2,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f373,f190])).

fof(f373,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k5_waybel_0(sK2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f372,f66])).

fof(f372,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k5_waybel_0(sK2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,X1)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f94,f69])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

fof(f819,plain,
    ( ~ r1_tarski(k5_waybel_0(sK2,sK8(sK2,sK3)),sK3)
    | sK3 = k5_waybel_0(sK2,sK4)
    | sK3 = k5_waybel_0(sK2,sK8(sK2,sK3)) ),
    inference(resolution,[],[f812,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f812,plain,
    ( r1_tarski(sK3,k5_waybel_0(sK2,sK8(sK2,sK3)))
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f807])).

fof(f807,plain,
    ( sK3 = k5_waybel_0(sK2,sK4)
    | r1_tarski(sK3,k5_waybel_0(sK2,sK8(sK2,sK3)))
    | r1_tarski(sK3,k5_waybel_0(sK2,sK8(sK2,sK3))) ),
    inference(resolution,[],[f741,f101])).

fof(f741,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK9(X7,k5_waybel_0(sK2,sK8(sK2,sK3))),sK3)
      | sK3 = k5_waybel_0(sK2,sK4)
      | r1_tarski(X7,k5_waybel_0(sK2,sK8(sK2,sK3))) ) ),
    inference(resolution,[],[f728,f102])).

fof(f728,plain,(
    ! [X1] :
      ( r2_hidden(X1,k5_waybel_0(sK2,sK8(sK2,sK3)))
      | sK3 = k5_waybel_0(sK2,sK4)
      | ~ r2_hidden(X1,sK3) ) ),
    inference(subsumption_resolution,[],[f727,f695])).

fof(f727,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | sK3 = k5_waybel_0(sK2,sK4)
      | ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2))
      | r2_hidden(X1,k5_waybel_0(sK2,sK8(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f724,f131])).

fof(f724,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | sK3 = k5_waybel_0(sK2,sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2))
      | r2_hidden(X1,k5_waybel_0(sK2,sK8(sK2,sK3))) ) ),
    inference(resolution,[],[f722,f394])).

fof(f394,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_hidden(X0,k5_waybel_0(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f393,f66])).

fof(f393,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_hidden(X0,k5_waybel_0(sK2,X1))
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f95,f69])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X2,k5_waybel_0(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f722,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,X0,sK8(sK2,sK3))
      | ~ r2_hidden(X0,sK3)
      | sK3 = k5_waybel_0(sK2,sK4) ) ),
    inference(subsumption_resolution,[],[f721,f695])).

fof(f721,plain,(
    ! [X0] :
      ( sK3 = k5_waybel_0(sK2,sK4)
      | ~ r2_hidden(X0,sK3)
      | r1_orders_2(sK2,X0,sK8(sK2,sK3))
      | ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f720,f131])).

fof(f720,plain,(
    ! [X0] :
      ( sK3 = k5_waybel_0(sK2,sK4)
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,sK8(sK2,sK3))
      | ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f719,f69])).

fof(f719,plain,(
    ! [X0] :
      ( sK3 = k5_waybel_0(sK2,sK4)
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,sK8(sK2,sK3))
      | ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f717,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
                & r2_hidden(sK7(X0,X1,X2),X1)
                & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
        & r2_hidden(sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f717,plain,
    ( r2_lattice3(sK2,sK3,sK8(sK2,sK3))
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f716,f70])).

fof(f716,plain,
    ( v1_xboole_0(sK3)
    | r2_lattice3(sK2,sK3,sK8(sK2,sK3))
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f715,f71])).

fof(f715,plain,
    ( ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_lattice3(sK2,sK3,sK8(sK2,sK3))
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f714,f72])).

fof(f714,plain,
    ( ~ v12_waybel_0(sK3,sK2)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_lattice3(sK2,sK3,sK8(sK2,sK3))
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f713,f73])).

fof(f713,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v12_waybel_0(sK3,sK2)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_lattice3(sK2,sK3,sK8(sK2,sK3))
    | sK3 = k5_waybel_0(sK2,sK4) ),
    inference(resolution,[],[f612,f75])).

fof(f612,plain,(
    ! [X0] :
      ( ~ v14_waybel_0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | r2_lattice3(sK2,X0,sK8(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f611,f66])).

fof(f611,plain,(
    ! [X0] :
      ( ~ v14_waybel_0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | r2_lattice3(sK2,X0,sK8(sK2,X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f610,f67])).

fof(f610,plain,(
    ! [X0] :
      ( ~ v14_waybel_0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | r2_lattice3(sK2,X0,sK8(sK2,X0))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f609,f69])).

fof(f609,plain,(
    ! [X0] :
      ( ~ v14_waybel_0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v12_waybel_0(X0,sK2)
      | ~ v1_waybel_0(X0,sK2)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(sK2)
      | r2_lattice3(sK2,X0,sK8(sK2,X0))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f92,f68])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ v14_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK8(X0,X1))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f76,plain,(
    ! [X2] :
      ( k5_waybel_0(sK2,X2) != sK3
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ v14_waybel_0(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f462,plain,
    ( r2_hidden(sK4,k5_waybel_0(sK2,sK4))
    | v14_waybel_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f461,f74])).

fof(f74,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | v14_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f461,plain,
    ( v14_waybel_0(sK3,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,k5_waybel_0(sK2,sK4)) ),
    inference(duplicate_literal_removal,[],[f458])).

fof(f458,plain,
    ( v14_waybel_0(sK3,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,k5_waybel_0(sK2,sK4)) ),
    inference(resolution,[],[f445,f394])).

fof(f445,plain,
    ( r1_orders_2(sK2,sK4,sK4)
    | v14_waybel_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f442,f74])).

fof(f442,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK4,sK4)
    | v14_waybel_0(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK4,sK4)
    | v14_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f406,f176])).

fof(f176,plain,
    ( r3_orders_2(sK2,sK4,sK4)
    | v14_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f174,f74])).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r3_orders_2(sK2,X0,X0) ) ),
    inference(subsumption_resolution,[],[f173,f66])).

fof(f173,plain,(
    ! [X0] :
      ( r3_orders_2(sK2,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f172,f69])).

fof(f172,plain,(
    ! [X0] :
      ( r3_orders_2(sK2,X0,X0)
      | ~ l1_orders_2(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f111,f67])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X1)
      | r3_orders_2(X1,X0,X0)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f406,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f405,f66])).

fof(f405,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f404,f69])).

fof(f404,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | r1_orders_2(sK2,X0,X1)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f106,f67])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f1939,plain,
    ( ~ v14_waybel_0(sK3,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(trivial_inequality_removal,[],[f1886])).

fof(f1886,plain,
    ( sK3 != sK3
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v14_waybel_0(sK3,sK2) ),
    inference(superposition,[],[f76,f1881])).

fof(f2010,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f2009,f1939])).

fof(f2009,plain,
    ( v14_waybel_0(sK3,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f2008,f66])).

fof(f2008,plain,
    ( v14_waybel_0(sK3,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f2007,f67])).

fof(f2007,plain,
    ( v14_waybel_0(sK3,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f2006,f68])).

fof(f2006,plain,
    ( v14_waybel_0(sK3,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f2005,f69])).

fof(f2005,plain,
    ( v14_waybel_0(sK3,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f2004,f70])).

fof(f2004,plain,
    ( v14_waybel_0(sK3,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f2003,f71])).

fof(f2003,plain,
    ( v14_waybel_0(sK3,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f2002,f72])).

fof(f2002,plain,
    ( v14_waybel_0(sK3,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v12_waybel_0(sK3,sK2)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f2001,f73])).

fof(f2001,plain,
    ( v14_waybel_0(sK3,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v12_waybel_0(sK3,sK2)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f1999])).

fof(f1999,plain,
    ( v14_waybel_0(sK3,sK2)
    | v14_waybel_0(sK3,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v12_waybel_0(sK3,sK2)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f1997,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | v14_waybel_0(X1,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1997,plain,
    ( r2_lattice3(sK2,sK3,sK4)
    | v14_waybel_0(sK3,sK2) ),
    inference(resolution,[],[f1915,f74])).

fof(f1915,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_lattice3(sK2,sK3,sK4) ),
    inference(superposition,[],[f797,f1881])).

fof(f797,plain,(
    ! [X6] :
      ( r2_lattice3(sK2,k5_waybel_0(sK2,X6),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f791,f69])).

fof(f791,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK2))
      | r2_lattice3(sK2,k5_waybel_0(sK2,X6),X6)
      | ~ l1_orders_2(sK2) ) ),
    inference(duplicate_literal_removal,[],[f790])).

fof(f790,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK2))
      | ~ m1_subset_1(X6,u1_struct_0(sK2))
      | r2_lattice3(sK2,k5_waybel_0(sK2,X6),X6)
      | r2_lattice3(sK2,k5_waybel_0(sK2,X6),X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f381,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f381,plain,(
    ! [X17,X16] :
      ( r1_orders_2(sK2,sK7(sK2,k5_waybel_0(sK2,X16),X17),X16)
      | ~ m1_subset_1(X16,u1_struct_0(sK2))
      | ~ m1_subset_1(X17,u1_struct_0(sK2))
      | r2_lattice3(sK2,k5_waybel_0(sK2,X16),X17) ) ),
    inference(resolution,[],[f374,f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(sK2,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_lattice3(sK2,X0,X1) ) ),
    inference(resolution,[],[f88,f69])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1978,plain,(
    ! [X0] :
      ( r2_hidden(sK4,sK3)
      | m1_subset_1(sK8(sK2,sK3),X0)
      | ~ r1_tarski(sK3,X0) ) ),
    inference(resolution,[],[f1954,f130])).

fof(f1954,plain,
    ( r2_hidden(sK8(sK2,sK3),sK3)
    | r2_hidden(sK4,sK3) ),
    inference(subsumption_resolution,[],[f1953,f70])).

fof(f1953,plain,
    ( r2_hidden(sK4,sK3)
    | v1_xboole_0(sK3)
    | r2_hidden(sK8(sK2,sK3),sK3) ),
    inference(subsumption_resolution,[],[f1952,f71])).

fof(f1952,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_hidden(sK8(sK2,sK3),sK3) ),
    inference(subsumption_resolution,[],[f1951,f72])).

fof(f1951,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v12_waybel_0(sK3,sK2)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_hidden(sK8(sK2,sK3),sK3) ),
    inference(subsumption_resolution,[],[f1942,f73])).

fof(f1942,plain,
    ( r2_hidden(sK4,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v12_waybel_0(sK3,sK2)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_hidden(sK8(sK2,sK3),sK3) ),
    inference(resolution,[],[f1882,f494])).

fof(f2479,plain,(
    ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2)) ),
    inference(trivial_inequality_removal,[],[f2477])).

fof(f2477,plain,
    ( sK3 != sK3
    | ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2)) ),
    inference(superposition,[],[f2013,f2280])).

fof(f2280,plain,(
    sK3 = k5_waybel_0(sK2,sK8(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f2048,f2278])).

fof(f2278,plain,(
    r1_tarski(sK3,k5_waybel_0(sK2,sK8(sK2,sK3))) ),
    inference(duplicate_literal_removal,[],[f2269])).

fof(f2269,plain,
    ( r1_tarski(sK3,k5_waybel_0(sK2,sK8(sK2,sK3)))
    | r1_tarski(sK3,k5_waybel_0(sK2,sK8(sK2,sK3))) ),
    inference(resolution,[],[f2108,f101])).

fof(f2108,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK9(X7,k5_waybel_0(sK2,sK8(sK2,sK3))),sK3)
      | r1_tarski(X7,k5_waybel_0(sK2,sK8(sK2,sK3))) ) ),
    inference(resolution,[],[f2099,f102])).

fof(f2099,plain,(
    ! [X1] :
      ( r2_hidden(X1,k5_waybel_0(sK2,sK8(sK2,sK3)))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(subsumption_resolution,[],[f2098,f131])).

fof(f2098,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_hidden(X1,k5_waybel_0(sK2,sK8(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f2095,f2058])).

fof(f2095,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2))
      | r2_hidden(X1,k5_waybel_0(sK2,sK8(sK2,sK3))) ) ),
    inference(resolution,[],[f2060,f394])).

fof(f2060,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,X0,sK8(sK2,sK3))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f2042,f2058])).

fof(f2042,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r1_orders_2(sK2,X0,sK8(sK2,sK3))
      | ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f2041,f131])).

fof(f2041,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,sK8(sK2,sK3))
      | ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f2040,f69])).

fof(f2040,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_orders_2(sK2,X0,sK8(sK2,sK3))
      | ~ m1_subset_1(sK8(sK2,sK3),u1_struct_0(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f2024,f86])).

fof(f2024,plain,(
    r2_lattice3(sK2,sK3,sK8(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f2023,f70])).

fof(f2023,plain,
    ( v1_xboole_0(sK3)
    | r2_lattice3(sK2,sK3,sK8(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f2022,f71])).

fof(f2022,plain,
    ( ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_lattice3(sK2,sK3,sK8(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f2021,f72])).

fof(f2021,plain,
    ( ~ v12_waybel_0(sK3,sK2)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_lattice3(sK2,sK3,sK8(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f2015,f73])).

fof(f2015,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v12_waybel_0(sK3,sK2)
    | ~ v1_waybel_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | r2_lattice3(sK2,sK3,sK8(sK2,sK3)) ),
    inference(resolution,[],[f2012,f612])).

fof(f2012,plain,(
    v14_waybel_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f74,f2011])).

fof(f2048,plain,
    ( ~ r1_tarski(sK3,k5_waybel_0(sK2,sK8(sK2,sK3)))
    | sK3 = k5_waybel_0(sK2,sK8(sK2,sK3)) ),
    inference(resolution,[],[f2032,f99])).

fof(f2032,plain,(
    r1_tarski(k5_waybel_0(sK2,sK8(sK2,sK3)),sK3) ),
    inference(subsumption_resolution,[],[f1977,f2029])).

fof(f1977,plain,
    ( r2_hidden(sK4,sK3)
    | r1_tarski(k5_waybel_0(sK2,sK8(sK2,sK3)),sK3) ),
    inference(resolution,[],[f1954,f1617])).

fof(f2013,plain,(
    ! [X2] :
      ( k5_waybel_0(sK2,X2) != sK3
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f76,f2012])).

%------------------------------------------------------------------------------
