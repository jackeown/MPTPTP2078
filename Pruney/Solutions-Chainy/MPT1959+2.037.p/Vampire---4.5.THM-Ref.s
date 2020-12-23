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
% DateTime   : Thu Dec  3 13:22:56 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 718 expanded)
%              Number of leaves         :    8 (  97 expanded)
%              Depth                    :   29
%              Number of atoms          :  277 (5284 expanded)
%              Number of equality atoms :   32 ( 163 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(subsumption_resolution,[],[f153,f111])).

fof(f111,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f33,f108])).

fof(f108,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f107,f33])).

fof(f107,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f104,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

% (5942)Refutation not found, incomplete strategy% (5942)------------------------------
% (5942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5942)Termination reason: Refutation not found, incomplete strategy

% (5942)Memory used [KB]: 10618
% (5963)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f104,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f70])).

fof(f70,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f60,f30])).

fof(f30,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f60,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

% (5964)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f103,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f33])).

fof(f102,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f100,f32])).

fof(f32,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | sK1 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f99,f61])).

% (5960)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f61,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f98,f37])).

fof(f37,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f98,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | ~ l1_orders_2(sK0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f97,f65])).

fof(f65,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f55,f54])).

fof(f54,plain,(
    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f37,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f97,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | ~ l1_orders_2(sK0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f92,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ l1_orders_2(X0)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f92,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1))
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f91,f34])).

% (5957)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,
    ( sK1 = u1_struct_0(sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f90,f37])).

fof(f90,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f89,f36])).

fof(f36,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f87,f35])).

fof(f35,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f61,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_orders_2(X0,k3_yellow_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f153,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f149,f53])).

fof(f53,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f149,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f126,f109])).

fof(f109,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,sK1) ),
    inference(backward_demodulation,[],[f29,f108])).

fof(f29,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f126,plain,(
    r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f125,f108])).

fof(f125,plain,(
    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f117,f31])).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f117,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f72,f108])).

fof(f72,plain,
    ( r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:12:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (5942)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (5955)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (5959)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (5944)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (5947)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (5961)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (5965)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (5953)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (5945)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (5949)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (5952)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (5943)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (5951)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.25/0.52  % (5947)Refutation found. Thanks to Tanya!
% 1.25/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.52  % SZS output start Proof for theBenchmark
% 1.25/0.52  fof(f154,plain,(
% 1.25/0.52    $false),
% 1.25/0.52    inference(subsumption_resolution,[],[f153,f111])).
% 1.25/0.52  fof(f111,plain,(
% 1.25/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 1.25/0.52    inference(backward_demodulation,[],[f33,f108])).
% 1.25/0.52  fof(f108,plain,(
% 1.25/0.52    sK1 = u1_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f107,f33])).
% 1.25/0.52  fof(f107,plain,(
% 1.25/0.52    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.25/0.52    inference(duplicate_literal_removal,[],[f105])).
% 1.25/0.52  fof(f105,plain,(
% 1.25/0.52    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f104,f40])).
% 1.25/0.52  fof(f40,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1) )),
% 1.25/0.52    inference(cnf_transformation,[],[f19])).
% 1.25/0.52  % (5942)Refutation not found, incomplete strategy% (5942)------------------------------
% 1.25/0.52  % (5942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (5942)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (5942)Memory used [KB]: 10618
% 1.25/0.52  % (5963)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.25/0.52  fof(f19,plain,(
% 1.25/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/0.52    inference(flattening,[],[f18])).
% 1.25/0.52  fof(f18,plain,(
% 1.25/0.52    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f1])).
% 1.25/0.52  fof(f1,axiom,(
% 1.25/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 1.25/0.52  fof(f104,plain,(
% 1.25/0.52    r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f103,f70])).
% 1.25/0.52  fof(f70,plain,(
% 1.25/0.52    r2_hidden(k3_yellow_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f60,f30])).
% 1.25/0.52  fof(f30,plain,(
% 1.25/0.52    ~v1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f15,plain,(
% 1.25/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.25/0.52    inference(flattening,[],[f14])).
% 1.25/0.52  fof(f14,plain,(
% 1.25/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f13])).
% 1.25/0.52  fof(f13,plain,(
% 1.25/0.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.25/0.52    inference(pure_predicate_removal,[],[f12])).
% 1.25/0.52  fof(f12,plain,(
% 1.25/0.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.25/0.52    inference(pure_predicate_removal,[],[f11])).
% 1.25/0.52  fof(f11,plain,(
% 1.25/0.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.25/0.52    inference(pure_predicate_removal,[],[f10])).
% 1.25/0.52  fof(f10,negated_conjecture,(
% 1.25/0.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.25/0.52    inference(negated_conjecture,[],[f9])).
% 1.25/0.52  fof(f9,conjecture,(
% 1.25/0.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.25/0.52  fof(f60,plain,(
% 1.25/0.52    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f33,f42])).
% 1.25/0.52  fof(f42,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f22])).
% 1.25/0.52  fof(f22,plain,(
% 1.25/0.52    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f8])).
% 1.25/0.52  % (5964)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.25/0.52  fof(f8,axiom,(
% 1.25/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.25/0.52  fof(f103,plain,(
% 1.25/0.52    ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f102,f33])).
% 1.25/0.52  fof(f102,plain,(
% 1.25/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f100,f32])).
% 1.25/0.52  fof(f32,plain,(
% 1.25/0.52    v13_waybel_0(sK1,sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f100,plain,(
% 1.25/0.52    ( ! [X0] : (~v13_waybel_0(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(k3_yellow_0(sK0),X0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | sK1 = u1_struct_0(sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f99,f61])).
% 1.25/0.52  % (5960)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.25/0.52  fof(f61,plain,(
% 1.25/0.52    m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 1.25/0.52    inference(resolution,[],[f33,f39])).
% 1.25/0.52  fof(f39,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK2(X0,X1),X0) | X0 = X1) )),
% 1.25/0.52    inference(cnf_transformation,[],[f19])).
% 1.25/0.52  fof(f99,plain,(
% 1.25/0.52    ( ! [X0] : (sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f98,f37])).
% 1.25/0.52  fof(f37,plain,(
% 1.25/0.52    l1_orders_2(sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f98,plain,(
% 1.25/0.52    ( ! [X0] : (sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f97,f65])).
% 1.25/0.52  fof(f65,plain,(
% 1.25/0.52    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.25/0.52    inference(superposition,[],[f55,f54])).
% 1.25/0.52  fof(f54,plain,(
% 1.25/0.52    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 1.25/0.52    inference(resolution,[],[f37,f52])).
% 1.25/0.52  fof(f52,plain,(
% 1.25/0.52    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f28])).
% 1.25/0.52  fof(f28,plain,(
% 1.25/0.52    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f4])).
% 1.25/0.52  fof(f4,axiom,(
% 1.25/0.52    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.25/0.52  fof(f55,plain,(
% 1.25/0.52    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))) )),
% 1.25/0.52    inference(resolution,[],[f37,f44])).
% 1.25/0.52  fof(f44,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f23])).
% 1.25/0.52  fof(f23,plain,(
% 1.25/0.52    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f5])).
% 1.25/0.52  fof(f5,axiom,(
% 1.25/0.52    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 1.25/0.52  fof(f97,plain,(
% 1.25/0.52    ( ! [X0] : (sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 1.25/0.52    inference(resolution,[],[f92,f49])).
% 1.25/0.52  fof(f49,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~l1_orders_2(X0) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f25])).
% 1.25/0.52  fof(f25,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.25/0.52    inference(flattening,[],[f24])).
% 1.25/0.52  fof(f24,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f7])).
% 1.25/0.52  fof(f7,axiom,(
% 1.25/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.25/0.52  fof(f92,plain,(
% 1.25/0.52    r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1)) | sK1 = u1_struct_0(sK0)),
% 1.25/0.52    inference(subsumption_resolution,[],[f91,f34])).
% 1.25/0.52  % (5957)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.25/0.52  fof(f34,plain,(
% 1.25/0.52    ~v2_struct_0(sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f91,plain,(
% 1.25/0.52    sK1 = u1_struct_0(sK0) | v2_struct_0(sK0) | r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1))),
% 1.25/0.52    inference(subsumption_resolution,[],[f90,f37])).
% 1.25/0.52  fof(f90,plain,(
% 1.25/0.52    sK1 = u1_struct_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1))),
% 1.25/0.52    inference(subsumption_resolution,[],[f89,f36])).
% 1.25/0.52  fof(f36,plain,(
% 1.25/0.52    v1_yellow_0(sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f89,plain,(
% 1.25/0.52    sK1 = u1_struct_0(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1))),
% 1.25/0.52    inference(subsumption_resolution,[],[f87,f35])).
% 1.25/0.52  fof(f35,plain,(
% 1.25/0.52    v5_orders_2(sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f87,plain,(
% 1.25/0.52    sK1 = u1_struct_0(sK0) | ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1))),
% 1.25/0.52    inference(resolution,[],[f61,f41])).
% 1.25/0.52  fof(f41,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,k3_yellow_0(X0),X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f21])).
% 1.25/0.52  fof(f21,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.25/0.52    inference(flattening,[],[f20])).
% 1.25/0.52  fof(f20,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f6])).
% 1.25/0.52  fof(f6,axiom,(
% 1.25/0.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).
% 1.25/0.52  fof(f33,plain,(
% 1.25/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f153,plain,(
% 1.25/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 1.25/0.52    inference(resolution,[],[f149,f53])).
% 1.25/0.52  fof(f53,plain,(
% 1.25/0.52    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 1.25/0.52    inference(equality_resolution,[],[f43])).
% 1.25/0.52  fof(f43,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f22])).
% 1.25/0.52  fof(f149,plain,(
% 1.25/0.52    v1_subset_1(sK1,sK1)),
% 1.25/0.52    inference(resolution,[],[f126,f109])).
% 1.25/0.52  fof(f109,plain,(
% 1.25/0.52    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,sK1)),
% 1.25/0.52    inference(backward_demodulation,[],[f29,f108])).
% 1.25/0.52  fof(f29,plain,(
% 1.25/0.52    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f126,plain,(
% 1.25/0.52    r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.25/0.52    inference(forward_demodulation,[],[f125,f108])).
% 1.25/0.52  fof(f125,plain,(
% 1.25/0.52    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.25/0.52    inference(subsumption_resolution,[],[f117,f31])).
% 1.25/0.52  fof(f31,plain,(
% 1.25/0.52    ~v1_xboole_0(sK1)),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f117,plain,(
% 1.25/0.52    v1_xboole_0(sK1) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.25/0.52    inference(backward_demodulation,[],[f72,f108])).
% 1.25/0.52  fof(f72,plain,(
% 1.25/0.52    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.25/0.52    inference(resolution,[],[f65,f51])).
% 1.25/0.52  fof(f51,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f27])).
% 1.25/0.52  fof(f27,plain,(
% 1.25/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.25/0.52    inference(flattening,[],[f26])).
% 1.25/0.52  fof(f26,plain,(
% 1.25/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.25/0.52    inference(ennf_transformation,[],[f2])).
% 1.25/0.52  fof(f2,axiom,(
% 1.25/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.25/0.52  % SZS output end Proof for theBenchmark
% 1.25/0.52  % (5947)------------------------------
% 1.25/0.52  % (5947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (5947)Termination reason: Refutation
% 1.25/0.52  
% 1.25/0.52  % (5947)Memory used [KB]: 6140
% 1.25/0.52  % (5947)Time elapsed: 0.108 s
% 1.25/0.52  % (5947)------------------------------
% 1.25/0.52  % (5947)------------------------------
% 1.25/0.53  % (5941)Success in time 0.162 s
%------------------------------------------------------------------------------
