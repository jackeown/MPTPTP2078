%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 506 expanded)
%              Number of leaves         :   14 (  99 expanded)
%              Depth                    :   24
%              Number of atoms          :  333 (3297 expanded)
%              Number of equality atoms :   25 (  88 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(subsumption_resolution,[],[f255,f256])).

fof(f256,plain,(
    ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f216,f252])).

fof(f252,plain,(
    ~ v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f218,f78])).

fof(f78,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f218,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f39,f213])).

fof(f213,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f212,f98])).

fof(f98,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f96,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f96,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f39,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f212,plain,
    ( sK1 = u1_struct_0(sK0)
    | r1_tarski(u1_struct_0(sK0),sK1) ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( sK1 = u1_struct_0(sK0)
    | r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f205,f120])).

fof(f120,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f111,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f111,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f98,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

% (24659)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f205,plain,(
    ! [X6] :
      ( ~ m1_subset_1(sK5(X6,sK1),u1_struct_0(sK0))
      | sK1 = u1_struct_0(sK0)
      | r1_tarski(X6,sK1) ) ),
    inference(resolution,[],[f196,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f196,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f192,f110])).

fof(f110,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f97,f35])).

fof(f35,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f97,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f39,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f192,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f187,f39])).

fof(f187,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f158,f38])).

fof(f38,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X1,sK0)
      | ~ r2_hidden(k3_yellow_0(sK0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,X1)
      | ~ v13_waybel_0(X1,sK0) ) ),
    inference(resolution,[],[f156,f95])).

fof(f95,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_orders_2(sK0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r2_hidden(X6,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X7,X5)
      | ~ v13_waybel_0(X5,sK0) ) ),
    inference(subsumption_resolution,[],[f91,f75])).

fof(f75,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f91,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r2_hidden(X6,X5)
      | ~ r1_orders_2(sK0,X6,X7)
      | r2_hidden(X7,X5)
      | ~ v13_waybel_0(X5,sK0) ) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f45,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f156,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f155,f85])).

fof(f85,plain,(
    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) ) ),
    inference(subsumption_resolution,[],[f154,f86])).

fof(f86,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,k1_xboole_0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f45,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_lattice3(X0,k1_xboole_0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f154,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k1_xboole_0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f107,f99])).

fof(f99,plain,(
    r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f84,f45])).

fof(f84,plain,
    ( ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f82,f43])).

fof(f43,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f44,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f44,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK0,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) ) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ r1_yellow_0(sK0,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) ) ),
    inference(resolution,[],[f94,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

% (24647)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f94,plain,(
    ! [X12] : m1_subset_1(k1_yellow_0(sK0,X12),u1_struct_0(sK0)) ),
    inference(resolution,[],[f45,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f216,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f34,f213])).

fof(f34,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f255,plain,(
    r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(resolution,[],[f230,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f36,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f36,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f230,plain,(
    m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f106,f213])).

fof(f106,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f94,f85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:33:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (24642)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (24658)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (24656)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (24641)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (24648)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (24650)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (24658)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (24665)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.53  % (24637)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.53  % (24639)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.53  % (24638)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.53  % (24657)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.53  % (24655)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.53  % (24646)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.53  % (24644)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.54  % (24640)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.54  % (24645)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.54  % SZS output start Proof for theBenchmark
% 1.39/0.54  fof(f257,plain,(
% 1.39/0.54    $false),
% 1.39/0.54    inference(subsumption_resolution,[],[f255,f256])).
% 1.39/0.54  fof(f256,plain,(
% 1.39/0.54    ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.39/0.54    inference(subsumption_resolution,[],[f216,f252])).
% 1.39/0.54  fof(f252,plain,(
% 1.39/0.54    ~v1_subset_1(sK1,sK1)),
% 1.39/0.54    inference(resolution,[],[f218,f78])).
% 1.39/0.54  fof(f78,plain,(
% 1.39/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.39/0.54    inference(equality_resolution,[],[f66])).
% 1.39/0.54  fof(f66,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f30])).
% 1.39/0.54  fof(f30,plain,(
% 1.39/0.54    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f13])).
% 1.39/0.54  fof(f13,axiom,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.39/0.54  fof(f218,plain,(
% 1.39/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 1.39/0.54    inference(backward_demodulation,[],[f39,f213])).
% 1.39/0.54  fof(f213,plain,(
% 1.39/0.54    sK1 = u1_struct_0(sK0)),
% 1.39/0.54    inference(subsumption_resolution,[],[f212,f98])).
% 1.39/0.54  fof(f98,plain,(
% 1.39/0.54    ~r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 1.39/0.54    inference(resolution,[],[f96,f69])).
% 1.39/0.54  fof(f69,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f2])).
% 1.39/0.54  fof(f2,axiom,(
% 1.39/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.54  fof(f96,plain,(
% 1.39/0.54    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.39/0.54    inference(resolution,[],[f39,f74])).
% 1.39/0.54  fof(f74,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,axiom,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.54  fof(f212,plain,(
% 1.39/0.54    sK1 = u1_struct_0(sK0) | r1_tarski(u1_struct_0(sK0),sK1)),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f207])).
% 1.39/0.54  fof(f207,plain,(
% 1.39/0.54    sK1 = u1_struct_0(sK0) | r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 1.39/0.54    inference(resolution,[],[f205,f120])).
% 1.39/0.54  fof(f120,plain,(
% 1.39/0.54    m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 1.39/0.54    inference(resolution,[],[f111,f63])).
% 1.39/0.54  fof(f63,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f27])).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f3])).
% 1.39/0.54  fof(f3,axiom,(
% 1.39/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.39/0.54  fof(f111,plain,(
% 1.39/0.54    r2_hidden(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 1.39/0.54    inference(resolution,[],[f98,f71])).
% 1.39/0.54  fof(f71,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f31])).
% 1.39/0.54  fof(f31,plain,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f1])).
% 1.39/0.54  fof(f1,axiom,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.54  % (24659)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.54  fof(f205,plain,(
% 1.39/0.54    ( ! [X6] : (~m1_subset_1(sK5(X6,sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | r1_tarski(X6,sK1)) )),
% 1.39/0.54    inference(resolution,[],[f196,f72])).
% 1.39/0.54  fof(f72,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f31])).
% 1.39/0.54  fof(f196,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)) )),
% 1.39/0.54    inference(resolution,[],[f192,f110])).
% 1.39/0.54  fof(f110,plain,(
% 1.39/0.54    r2_hidden(k3_yellow_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 1.39/0.54    inference(resolution,[],[f97,f35])).
% 1.39/0.54  fof(f35,plain,(
% 1.39/0.54    ~v1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.39/0.54    inference(flattening,[],[f16])).
% 1.39/0.54  fof(f16,plain,(
% 1.39/0.54    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f15])).
% 1.39/0.54  fof(f15,negated_conjecture,(
% 1.39/0.54    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.39/0.54    inference(negated_conjecture,[],[f14])).
% 1.39/0.54  fof(f14,conjecture,(
% 1.39/0.54    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.39/0.54  fof(f97,plain,(
% 1.39/0.54    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 1.39/0.54    inference(resolution,[],[f39,f65])).
% 1.39/0.54  fof(f65,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f30])).
% 1.39/0.54  fof(f192,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f187,f39])).
% 1.39/0.54  fof(f187,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.39/0.54    inference(resolution,[],[f158,f38])).
% 1.39/0.54  fof(f38,plain,(
% 1.39/0.54    v13_waybel_0(sK1,sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f158,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~v13_waybel_0(X1,sK0) | ~r2_hidden(k3_yellow_0(sK0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f157])).
% 1.39/0.54  fof(f157,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,X1) | ~v13_waybel_0(X1,sK0)) )),
% 1.39/0.54    inference(resolution,[],[f156,f95])).
% 1.39/0.54  fof(f95,plain,(
% 1.39/0.54    ( ! [X6,X7,X5] : (~r1_orders_2(sK0,X6,X7) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X7,X5) | ~v13_waybel_0(X5,sK0)) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f91,f75])).
% 1.39/0.54  fof(f75,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f33])).
% 1.39/0.54  fof(f33,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.39/0.54    inference(flattening,[],[f32])).
% 1.39/0.54  fof(f32,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.39/0.54    inference(ennf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.39/0.54  fof(f91,plain,(
% 1.39/0.54    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | ~r1_orders_2(sK0,X6,X7) | r2_hidden(X7,X5) | ~v13_waybel_0(X5,sK0)) )),
% 1.39/0.54    inference(resolution,[],[f45,f53])).
% 1.39/0.54  fof(f53,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f21])).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.39/0.54    inference(flattening,[],[f20])).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f12])).
% 1.39/0.54  fof(f12,axiom,(
% 1.39/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.39/0.54  fof(f45,plain,(
% 1.39/0.54    l1_orders_2(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f156,plain,(
% 1.39/0.54    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.39/0.54    inference(forward_demodulation,[],[f155,f85])).
% 1.39/0.54  fof(f85,plain,(
% 1.39/0.54    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 1.39/0.54    inference(resolution,[],[f45,f46])).
% 1.39/0.54  fof(f46,plain,(
% 1.39/0.54    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f18])).
% 1.39/0.54  fof(f18,plain,(
% 1.39/0.54    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f7])).
% 1.39/0.54  fof(f7,axiom,(
% 1.39/0.54    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.39/0.54  fof(f155,plain,(
% 1.39/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f154,f86])).
% 1.39/0.54  fof(f86,plain,(
% 1.39/0.54    ( ! [X0] : (r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.39/0.54    inference(resolution,[],[f45,f47])).
% 1.39/0.54  fof(f47,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_lattice3(X0,k1_xboole_0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f19])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : ((r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f11])).
% 1.39/0.54  fof(f11,axiom,(
% 1.39/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).
% 1.39/0.54  fof(f154,plain,(
% 1.39/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)) )),
% 1.39/0.54    inference(resolution,[],[f107,f99])).
% 1.39/0.54  fof(f99,plain,(
% 1.39/0.54    r1_yellow_0(sK0,k1_xboole_0)),
% 1.39/0.54    inference(subsumption_resolution,[],[f84,f45])).
% 1.39/0.54  fof(f84,plain,(
% 1.39/0.54    ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 1.39/0.54    inference(subsumption_resolution,[],[f83,f40])).
% 1.39/0.54  fof(f40,plain,(
% 1.39/0.54    ~v2_struct_0(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f83,plain,(
% 1.39/0.54    v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 1.39/0.54    inference(subsumption_resolution,[],[f82,f43])).
% 1.39/0.54  fof(f43,plain,(
% 1.39/0.54    v5_orders_2(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f82,plain,(
% 1.39/0.54    ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 1.39/0.54    inference(resolution,[],[f44,f60])).
% 1.39/0.54  fof(f60,plain,(
% 1.39/0.54    ( ! [X0] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,k1_xboole_0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f25])).
% 1.39/0.54  fof(f25,plain,(
% 1.39/0.54    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.39/0.54    inference(flattening,[],[f24])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f10])).
% 1.39/0.54  fof(f10,axiom,(
% 1.39/0.54    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).
% 1.39/0.54  fof(f44,plain,(
% 1.39/0.54    v1_yellow_0(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f107,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f104,f45])).
% 1.39/0.54  fof(f104,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) )),
% 1.39/0.54    inference(resolution,[],[f94,f77])).
% 1.39/0.54  fof(f77,plain,(
% 1.39/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)) )),
% 1.39/0.54    inference(equality_resolution,[],[f58])).
% 1.39/0.54  fof(f58,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 1.39/0.54    inference(cnf_transformation,[],[f23])).
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.54    inference(flattening,[],[f22])).
% 1.39/0.54  % (24647)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f8])).
% 1.39/0.54  fof(f8,axiom,(
% 1.39/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).
% 1.39/0.54  fof(f94,plain,(
% 1.39/0.54    ( ! [X12] : (m1_subset_1(k1_yellow_0(sK0,X12),u1_struct_0(sK0))) )),
% 1.39/0.54    inference(resolution,[],[f45,f62])).
% 1.39/0.54  fof(f62,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f26])).
% 1.39/0.54  fof(f26,plain,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f9])).
% 1.39/0.54  fof(f9,axiom,(
% 1.39/0.54    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 1.39/0.54  fof(f39,plain,(
% 1.39/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f216,plain,(
% 1.39/0.54    v1_subset_1(sK1,sK1) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.39/0.54    inference(backward_demodulation,[],[f34,f213])).
% 1.39/0.54  fof(f34,plain,(
% 1.39/0.54    v1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f255,plain,(
% 1.39/0.54    r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.39/0.54    inference(resolution,[],[f230,f81])).
% 1.39/0.54  fof(f81,plain,(
% 1.39/0.54    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(X0,sK1)) )),
% 1.39/0.54    inference(resolution,[],[f36,f64])).
% 1.39/0.54  fof(f64,plain,(
% 1.39/0.54    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f29])).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.39/0.54    inference(flattening,[],[f28])).
% 1.39/0.54  fof(f28,plain,(
% 1.39/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,axiom,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.39/0.54  fof(f36,plain,(
% 1.39/0.54    ~v1_xboole_0(sK1)),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f230,plain,(
% 1.39/0.54    m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.39/0.54    inference(backward_demodulation,[],[f106,f213])).
% 1.39/0.54  fof(f106,plain,(
% 1.39/0.54    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.39/0.54    inference(superposition,[],[f94,f85])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (24658)------------------------------
% 1.39/0.54  % (24658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (24658)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (24658)Memory used [KB]: 1791
% 1.39/0.54  % (24658)Time elapsed: 0.121 s
% 1.39/0.54  % (24658)------------------------------
% 1.39/0.54  % (24658)------------------------------
% 1.39/0.54  % (24649)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.54  % (24636)Success in time 0.185 s
%------------------------------------------------------------------------------
