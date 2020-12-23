%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2043+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 112 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   21
%              Number of atoms          :  347 ( 806 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(resolution,[],[f81,f28])).

fof(f28,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( v1_xboole_0(sK2)
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v13_waybel_0(sK1,k3_yellow_1(sK0))
    & v2_waybel_0(sK1,k3_yellow_1(sK0))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
          & v13_waybel_0(X1,k3_yellow_1(sK0))
          & v2_waybel_0(X1,k3_yellow_1(sK0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( v1_xboole_0(X2)
            & r2_hidden(X2,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
        & v13_waybel_0(X1,k3_yellow_1(sK0))
        & v2_waybel_0(X1,k3_yellow_1(sK0))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( v1_xboole_0(X2)
          & r2_hidden(X2,sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      & v13_waybel_0(sK1,k3_yellow_1(sK0))
      & v2_waybel_0(sK1,k3_yellow_1(sK0))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( v1_xboole_0(X2)
        & r2_hidden(X2,sK1) )
   => ( v1_xboole_0(sK2)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
              & v13_waybel_0(X1,k3_yellow_1(X0))
              & v2_waybel_0(X1,k3_yellow_1(X0))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ~ ( v1_xboole_0(X2)
                  & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(f81,plain,(
    v1_xboole_0(sK1) ),
    inference(resolution,[],[f80,f36])).

fof(f36,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f80,plain,
    ( v2_struct_0(k3_yellow_1(sK0))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f79,f30])).

fof(f30,plain,(
    v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
    | v1_xboole_0(sK1)
    | v2_struct_0(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f76,f31])).

fof(f31,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,
    ( ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(resolution,[],[f75,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | v1_xboole_0(sK1)
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(resolution,[],[f74,f29])).

fof(f29,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(sK1)
      | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
      | v2_struct_0(k3_yellow_1(X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(sK1,k3_yellow_1(X0)) ) ),
    inference(resolution,[],[f73,f57])).

fof(f57,plain,(
    r2_hidden(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f33,f56])).

fof(f56,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f52,f34])).

fof(f34,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f33,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X0,k3_yellow_1(X1)) ) ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(k3_yellow_1(X1))
      | v1_xboole_0(X0)
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ r2_hidden(k1_xboole_0,X0)
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X0,k3_yellow_1(X1)) ) ),
    inference(resolution,[],[f70,f38])).

fof(f38,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(k3_yellow_1(X1))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ r2_hidden(k1_xboole_0,X0)
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X0,k3_yellow_1(X1)) ) ),
    inference(resolution,[],[f69,f42])).

fof(f42,plain,(
    ! [X0] : v3_lattice3(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_lattice3(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_yellow_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v3_lattice3(k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ r2_hidden(k1_xboole_0,X0)
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X0,k3_yellow_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ r2_hidden(k1_xboole_0,X0)
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v3_lattice3(k3_yellow_1(X1))
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ l1_orders_2(k3_yellow_1(X1)) ) ),
    inference(resolution,[],[f67,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v25_waybel_0(X0)
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_lattice3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v25_waybel_0(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc11_waybel_0)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v25_waybel_0(k3_yellow_1(X1))
      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ r2_hidden(k1_xboole_0,X0)
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ r2_hidden(k1_xboole_0,X0)
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ v25_waybel_0(k3_yellow_1(X1))
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1))
      | ~ l1_orders_2(k3_yellow_1(X1)) ) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v25_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v25_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v25_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v25_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_yellow_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc12_waybel_0)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_0(k3_yellow_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ r2_hidden(k1_xboole_0,X0)
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1)) ) ),
    inference(resolution,[],[f62,f39])).

fof(f39,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(k3_yellow_1(X1))
      | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(k3_yellow_1(X1))
      | ~ v1_yellow_0(k3_yellow_1(X1))
      | ~ r2_hidden(k1_xboole_0,X0)
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1)) ) ),
    inference(forward_demodulation,[],[f61,f35])).

fof(f35,plain,(
    ! [X0] : k3_yellow_0(k3_yellow_1(X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_yellow_0(k3_yellow_1(X0)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(k3_yellow_1(X1))
      | ~ v1_yellow_0(k3_yellow_1(X1))
      | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X1)),X0)
      | ~ v4_orders_2(k3_yellow_1(X1))
      | ~ v3_orders_2(k3_yellow_1(X1))
      | v2_struct_0(k3_yellow_1(X1)) ) ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ r2_hidden(k3_yellow_0(X0),X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_subset_1(X1,u1_struct_0(X0))
              | r2_hidden(k3_yellow_0(X0),X1) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

%------------------------------------------------------------------------------
