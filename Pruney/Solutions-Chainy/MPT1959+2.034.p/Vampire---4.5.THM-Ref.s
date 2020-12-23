%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 998 expanded)
%              Number of leaves         :   10 ( 137 expanded)
%              Depth                    :   32
%              Number of atoms          :  346 (7144 expanded)
%              Number of equality atoms :   39 ( 227 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(subsumption_resolution,[],[f255,f217])).

fof(f217,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f40,f214])).

fof(f214,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f213,f40])).

fof(f213,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f204,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f204,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f203,f90])).

fof(f90,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f80,f37])).

fof(f37,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f80,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f40,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

% (10919)Refutation not found, incomplete strategy% (10919)------------------------------
% (10919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10919)Termination reason: Refutation not found, incomplete strategy

% (10919)Memory used [KB]: 10618
% (10919)Time elapsed: 0.083 s
% (10919)------------------------------
% (10919)------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f203,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f202,f40])).

fof(f202,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f153,f39])).

fof(f39,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | sK1 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f81])).

fof(f81,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f152,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f151,f44])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f151,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | ~ l1_orders_2(sK0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f150,f85])).

fof(f85,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f73,f74])).

% (10914)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (10922)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (10936)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (10920)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f74,plain,(
    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f44,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f44,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f150,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | ~ l1_orders_2(sK0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f147,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ l1_orders_2(X0)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f147,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1))
    | sK1 = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f146,f74])).

fof(f146,plain,
    ( sK1 = u1_struct_0(sK0)
    | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK2(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f145,f81])).

fof(f145,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK2(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f144,f44])).

fof(f144,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK2(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f143,f72])).

fof(f72,plain,(
    r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f71,f44])).

fof(f71,plain,
    ( ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f70,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f69,f42])).

fof(f42,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f43,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

% (10927)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (10935)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (10924)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (10928)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (10914)Refutation not found, incomplete strategy% (10914)------------------------------
% (10914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10914)Termination reason: Refutation not found, incomplete strategy

% (10914)Memory used [KB]: 10746
% (10914)Time elapsed: 0.095 s
% (10914)------------------------------
% (10914)------------------------------
fof(f43,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f143,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ r1_yellow_0(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK2(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f134,f73])).

fof(f134,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK2(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f123,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f123,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK2(u1_struct_0(sK0),sK1))
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f121,f44])).

fof(f121,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,k1_xboole_0,sK2(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f81,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,k1_xboole_0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f255,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f251,f66])).

fof(f66,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f251,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f237,f215])).

fof(f215,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,sK1) ),
    inference(backward_demodulation,[],[f36,f214])).

fof(f36,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f237,plain,(
    r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f236,f214])).

fof(f236,plain,(
    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f223,f38])).

fof(f38,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f223,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f88,f214])).

fof(f88,plain,
    ( r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f85,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (10918)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (10934)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (10932)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (10919)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (10918)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (10926)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f256,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f255,f217])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.50    inference(backward_demodulation,[],[f40,f214])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f213,f40])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f211])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f204,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f203,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    r2_hidden(k3_yellow_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f80,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ~v1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.50  fof(f12,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f11])).
% 0.20/0.50  fof(f11,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f40,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  % (10919)Refutation not found, incomplete strategy% (10919)------------------------------
% 0.20/0.50  % (10919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (10919)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (10919)Memory used [KB]: 10618
% 0.20/0.50  % (10919)Time elapsed: 0.083 s
% 0.20/0.50  % (10919)------------------------------
% 0.20/0.50  % (10919)------------------------------
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f202,f40])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f153,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    v13_waybel_0(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ( ! [X0] : (~v13_waybel_0(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(k3_yellow_0(sK0),X0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | sK1 = u1_struct_0(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f152,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f40,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK2(X0,X1),X0) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ( ! [X0] : (sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f151,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    l1_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    ( ! [X0] : (sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f150,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.50    inference(superposition,[],[f73,f74])).
% 0.20/0.50  % (10914)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (10922)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (10936)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (10920)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.51    inference(resolution,[],[f44,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))) )),
% 0.20/0.51    inference(resolution,[],[f44,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    ( ! [X0] : (sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 0.20/0.51    inference(resolution,[],[f147,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~l1_orders_2(X0) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.51    inference(forward_demodulation,[],[f146,f74])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    sK1 = u1_struct_0(sK0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK2(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f145,f81])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK2(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f144,f44])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK2(u1_struct_0(sK0),sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f143,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f71,f44])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f70,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f69,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    v5_orders_2(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.51    inference(resolution,[],[f43,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.20/0.51  % (10927)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (10935)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (10924)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (10928)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (10914)Refutation not found, incomplete strategy% (10914)------------------------------
% 0.20/0.52  % (10914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10914)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10914)Memory used [KB]: 10746
% 0.20/0.52  % (10914)Time elapsed: 0.095 s
% 0.20/0.52  % (10914)------------------------------
% 0.20/0.52  % (10914)------------------------------
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    v1_yellow_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    sK1 = u1_struct_0(sK0) | ~r1_yellow_0(sK0,k1_xboole_0) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK2(u1_struct_0(sK0),sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f134,f73])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    sK1 = u1_struct_0(sK0) | ~m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),sK2(u1_struct_0(sK0),sK1))),
% 0.20/0.52    inference(resolution,[],[f123,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_lattice3(X0,X1,X3) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)) )),
% 0.20/0.52    inference(equality_resolution,[],[f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(flattening,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    r2_lattice3(sK0,k1_xboole_0,sK2(u1_struct_0(sK0),sK1)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f121,f44])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    sK1 = u1_struct_0(sK0) | ~l1_orders_2(sK0) | r2_lattice3(sK0,k1_xboole_0,sK2(u1_struct_0(sK0),sK1))),
% 0.20/0.52    inference(resolution,[],[f81,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,k1_xboole_0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f255,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.52    inference(resolution,[],[f251,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f251,plain,(
% 0.20/0.52    v1_subset_1(sK1,sK1)),
% 0.20/0.52    inference(resolution,[],[f237,f215])).
% 0.20/0.52  fof(f215,plain,(
% 0.20/0.52    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f36,f214])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f236,f214])).
% 0.20/0.52  fof(f236,plain,(
% 0.20/0.52    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f223,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ~v1_xboole_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f223,plain,(
% 0.20/0.52    v1_xboole_0(sK1) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.52    inference(backward_demodulation,[],[f88,f214])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.52    inference(resolution,[],[f85,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (10918)------------------------------
% 0.20/0.52  % (10918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10918)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (10918)Memory used [KB]: 6268
% 0.20/0.52  % (10918)Time elapsed: 0.092 s
% 0.20/0.52  % (10918)------------------------------
% 0.20/0.52  % (10918)------------------------------
% 0.20/0.52  % (10912)Success in time 0.158 s
%------------------------------------------------------------------------------
